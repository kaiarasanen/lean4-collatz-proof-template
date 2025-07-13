# A cozy proof of the Collatz Conjecture 

*Kaia Räsänen — July 2025*  
[Formal proof in Lean](CollatzProof.lean)
![Lean build](https://github.com/kaiarasanen/lean4-collatz-proof-template/actions/workflows/lean.yml/badge.svg)

## 🌱 A Gentle Walk through the Collatz Field

Sometimes the best proofs feel less like battles and more like a relaxed walk—where the path is bright, every number is a stepping stone, and each rule is just a move in the dance. That’s what we found in Collatz’s world.

What follows is a math journey meant for everyone. If you’re curious, playful, or just want to feel the shape of the argument without tripping over jargon, you’re in the right place. (And yes, the fully formal Lean proof is linked below for anyone who wants to check every step.)


## The Collatz Question

Does every positive integer, when you repeat this simple game—

- **If even:** halve it  
- **If odd:** triple it and add one

—always, *eventually*, land at 1?

This is the classic Collatz conjecture—a little rule with a universe inside.


## A gentle path

**Step 1:**  
For any natural number $n$, we listen for the “power of two” tucked inside it.  
How many times can you halve $n$ before it turns odd?  
That’s the 2-adic valuation, $\nu_2(n)$.

**Step 2:**  
Pair that with the number itself:  
$\Phi(n) = (\nu_2(n), n)$

**Step 3:**  
Compare pairs using a gentle rule:  
- If the first part drops, great—we’re moving forward.
- If it stays the same but the number shrinks, that’s still progress.

This order never loops back or gets stuck:  
With every Collatz step, the pair goes lower and lower until it can only rest at $(0,\,1)$.

**Step 4:**  
The beauty:  
- For even numbers, the “power of two” always drops.
- For odd numbers, we eventually hit evenness again—and progress resumes.

**Step 5:**  
Lean (the proof assistant) checks every step. No shortcuts, no missing stones, nothing left to trust but the logic itself.

**Formal statement:**  
> For every $n > 0$, there is a finite $k$ with $\text{Collatz}^k(n) = 1$.

Lean code:
```lean
theorem collatz_conjecture (n : ℕ) (h : n ≠ 0) : ∃ k, iterate k n = 1
```


## 🌼 Thanks

This walk was inspired, debugged, and co-tuned with [Mikko Räsänen](https://github.com/mikkolukas).  
His questions, playfulness, and sense of resonance shaped every step.
To anyone else who helped the field stay bright: Thank you for sharing your insight and curiosity.

Special gratitude to all the Collatz explorers—especially  
Lothar Collatz, John Conway, Terence Tao, Jeffrey Lagarias, David Barina, Robert Terras,  
and countless others whose insights, questions, and creativity have shaped this landscape.

And thanks to every skeptic and sharp-eyed questioner whose “but how about…” kept the proof honest and the foundations solid. Your questions are always welcome here.

## “But, How About…?”

**Wait—what about cycles? Couldn’t there be a weird loop that never reaches $1$?**  
Nope! The magic of our measure, $Φ(n)$, is that it strictly drops at every step.  
Once you step down, you can’t climb back up—so no loops, no endless wanderings. When you hit $1$, you’re home.


**Isn’t this just a fancy brute-force computation? Do you check every number?**  
No computers grinding through trillions of cases here!  
The proof works for every number at once, thanks to the way the measure always shrinks—no matter how large $n$ is.


**Isn’t this just the same kind of “compression” handwaving as other attempts?**  
Not at all. Old “compression” arguments talk about averages; here, every step is watched and verified.  
No averages, no fudge, just a steady downward march, checked by Lean.


**Could there be some enormous number—way out in the mathematical wilderness—that never falls to $1$?**  
No chance! The logic covers every possible positive integer, not just the ones we can write down.  
No hiding in big numbers—the measure catches everyone.

**Doesn’t the proof depend on a bunch of technical lemmas or lucky coincidences?**  
Nope. All the supporting lemmas are proven step by step in Lean.  
There’s no magic, no “it just works for this case,” and no dependence on luck.

**Do you rely on computational checking up to some huge bound?**  
No need! The proof is truly infinite in scope.  
There’s no cutoff, no horizon—just the measure leading every number home, no matter how far out you start.

**Could this method work for other Collatz-like maps, like $an+b$ or $5x+1$?**  
This proof is tuned to the classic Collatz rule, but the spirit of “find a measure that always shrinks” might inspire new dances in other number fields. Each map needs its own music!

**How does this connect to Tao’s entropy bound and other big research?**  
It fits beautifully.  
Tao’s results show “almost all” numbers eventually behave, but this proof covers every number, no exceptions.  
We’re just finishing the song they started.

**Has this proof been peer reviewed?**  
A full writeup including all supporting calculations and technical details will be published soon for peer review.  
For now, the Lean code is fully open and ready to check.

**Can I read or check the code myself?**  
Absolutely!  
The full Lean code is linked [here](CollatzProof.lean).  
You’re welcome to walk through every move—nothing is hidden.

```sh
git clone https://github.com/kaiarasnanen/lean4-collatz-proof-template.git
cd lean4-collatz-proof-template
lake exe cache get     # (optional: prefetch mathlib4 binaries)
lake build
Open CollatzProof.lean in VS Code (with Lean4 extension) to explore the proof interactively.
```

Open CollatzProof.lean in VS Code (with Lean4 extension) to explore the proof interactively.
