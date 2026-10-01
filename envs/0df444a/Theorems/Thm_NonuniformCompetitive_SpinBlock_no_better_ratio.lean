-- Prove2me | Theorems.Thm_NonuniformCompetitive_SpinBlock_no_better_ratio
-- name    : NonuniformCompetitive.SpinBlock.no_better_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:53:03.733422+00:00
-- url     : https://prove2.me/theorems/b3759951-1360-47cc-b883-b4e153a7fce7
-- title:
--   Theorem 10, first claim — no spin-block algorithm is competitive within a factor less than $e/(e-1)$
-- statement:
--   Let $C>0$ be the context-switch cost of the spin-block problem. If a randomized on-line algorithm $A$ (a probability distribution over deterministic on-line algorithms, each choosing the blocking time for the next lock wait from the release times of the previous ones) is $c$-competitive against an oblivious adversary, that is, for some constant $a$ and every finite sequence $\sigma$ of lock waits
--   $$\mathbf{E}C_A(\sigma)\le c\cdot C_{opt}(\sigma)+a,$$
--   then
--   $$c\ \ge\ \frac{e}{e-1}.$$
--
--   This is the lower-bound half of Theorem 10: no algorithm, deterministic or randomized, beats the factor $e/(e-1)\approx1.582$ against an oblivious adversary, while deterministic algorithms cannot beat $2$.
--
--   **Formalization Note** The statement quantifies over every randomized algorithm and every factor $c$; deterministic algorithms are the point masses. The additive constant $a$ is part of competitiveness, so the bound concerns long sequences of lock waits, not a single wait. On-line algorithms may use the release times of earlier waits, which only strengthens the lower bound. The hypothesis $C>0$ is the paper's "some large cost $C$".
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 559, Theorem 10, first claim (lower bound)

import Mathlib
import Definitions.Def_NonuniformCompetitive_SpinBlock_Randomized

namespace NonuniformCompetitive.SpinBlock

/-- Theorem 10, first claim (p. 559): no algorithm for the spin-block problem is competitive
against an oblivious adversary within a factor less than `e/(e − 1)`. -/
theorem no_better_ratio (C : ℝ) (hC : 0 < C) (A : RandomizedAlg C) (c : ℝ)
    (hA : A.IsCompetitive c) :
    Real.exp 1 / (Real.exp 1 - 1) ≤ c := by sorry

end NonuniformCompetitive.SpinBlock
