-- Prove2me | Theorems.Thm_NonuniformCompetitive_SpinBlock_ratio_attained
-- name    : NonuniformCompetitive.SpinBlock.ratio_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:53:28.01411+00:00
-- url     : https://prove2.me/theorems/ea58ec71-b206-4a66-b08e-96bb516c111e
-- title:
--   Theorem 10, second claim — a randomized spin-block algorithm is $e/(e-1)$-competitive
-- statement:
--   Let $C>0$ be the context-switch cost of the spin-block problem. There is a randomized on-line algorithm $A$ and a constant $a$ such that for every finite sequence $\sigma$ of lock waits
--   $$\mathbf{E}C_A(\sigma)\le\frac{e}{e-1}\,C_{opt}(\sigma)+a,$$
--   that is, $A$ is $\frac{e}{e-1}$-competitive against an oblivious adversary.
--
--   This is the attainment half of Theorem 10; together with the lower bound it shows that $e/(e-1)$ is the optimal randomized competitive factor.
--
--   **Formalization Note** The randomized algorithm is a probability distribution over deterministic on-line algorithms whose cost on each fixed input is a measurable function of the random outcome, so the expected cost is a genuine expectation. The hypothesis $C>0$ is the paper's "some large cost $C$".
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 559, Theorem 10, second claim (attainment); pp. 559–560, proof

import Mathlib
import Definitions.Def_NonuniformCompetitive_SpinBlock_Randomized

namespace NonuniformCompetitive.SpinBlock

/-- Theorem 10, second claim (p. 559): there is a randomized algorithm for the spin-block problem
that is `e/(e − 1)`-competitive against an oblivious adversary. -/
theorem ratio_attained (C : ℝ) (hC : 0 < C) :
    ∃ A : RandomizedAlg C, A.IsCompetitive (Real.exp 1 / (Real.exp 1 - 1)) := by sorry

end NonuniformCompetitive.SpinBlock
