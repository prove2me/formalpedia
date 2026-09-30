-- Prove2me | Theorems.Thm_NonuniformCompetitive_SpinBlock_optimal_ratio
-- name    : NonuniformCompetitive.SpinBlock.optimal_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:53:48.812683+00:00
-- url     : https://prove2.me/theorems/1e13f22e-d9bf-419f-aacc-884ce76ebec5
-- title:
--   Theorem 10 — the spin-block problem is optimally $e/(e-1)$-competitive against an oblivious adversary
-- statement:
--   Consider the spin-block problem with context-switch cost $C>0$: for each of a sequence of lock waits, an on-line algorithm chooses how long to spin (cost $1$ per unit time) before blocking (cost $C$), not knowing when the lock will be released; the off-line optimum pays $\min(\tau,C)$ for a lock released at time $\tau$. Then
--
--   1. no randomized on-line algorithm is $c$-competitive against an oblivious adversary for any $c<\frac{e}{e-1}$: if $\mathbf{E}C_A(\sigma)\le c\cdot C_{opt}(\sigma)+a$ for some constant $a$ and all input sequences $\sigma$, then $c\ge\frac{e}{e-1}$;
--   2. there is a randomized on-line algorithm that is $\frac{e}{e-1}$-competitive against an oblivious adversary.
--
--   $$\inf\{c : \text{some randomized algorithm is } c\text{-competitive}\}=\frac{e}{e-1}\approx1.582,\ \text{and the infimum is attained.}$$
--
--   This is Theorem 10 of Karlin, Manasse, McGeoch and Owicki, the continuous (ski-rental) counterpart of their optimal randomized snoopy-caching bound; the deterministic optimum is $2$.
--
--   **Formalization Note** Randomized algorithms are mixed strategies over deterministic on-line algorithms, each of which chooses the next blocking time from the release times of earlier waits; the cost on each fixed input is required to be measurable in the random outcome. Competitiveness carries an additive constant, as defined in §1 of the paper. The hypothesis $C>0$ is the paper's "some large cost $C$"; at $C=0$ blocking at once is free and optimal.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 559, Theorem 10

import Mathlib
import Definitions.Def_NonuniformCompetitive_SpinBlock_Randomized

namespace NonuniformCompetitive.SpinBlock

/-- Theorem 10 (p. 559): no algorithm for the spin-block problem is competitive against an
oblivious adversary within a factor less than `e/(e − 1)`, and there is a randomized algorithm
that achieves this competitive factor. -/
theorem optimal_ratio (C : ℝ) (hC : 0 < C) :
    (∀ (A : RandomizedAlg C) (c : ℝ), A.IsCompetitive c → Real.exp 1 / (Real.exp 1 - 1) ≤ c) ∧
      ∃ A : RandomizedAlg C, A.IsCompetitive (Real.exp 1 / (Real.exp 1 - 1)) := by sorry

end NonuniformCompetitive.SpinBlock
