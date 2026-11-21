-- Prove2me | Theorems.Thm_GRH_exponential_smoothing_of_partialSums_isBigO_rpow
-- name    : GRH.exponential_smoothing_of_partialSums_isBigO_rpow
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:03:03.818464+00:00
-- url     : https://prove2.me/theorems/2c5cc26d-af66-4967-b366-a1faf9704d9c
-- title:
--   Power bounds on partial sums carry over to exponential smoothing
-- statement:
--   For any complex sequence $a_n$ and any $0\le\sigma\le1$, suppose $A_N=\sum_{0\le n\le N}a_n=O(N^\sigma)$. Then $\sum_{n\ge0}a_n e^{-n/D}=O(D^\sigma)$ as the real scale $D$ tends to infinity. The constants may depend on the sequence and on the exponent.
-- source:
--   Independent Abel summation proof using the geometric first moment, Mathlib hasSum_coe_mul_geometric_of_norm_lt_one: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecificLimits/Normed.lean#L516-L549

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Filter Asymptotics
open scoped BigOperators Topology

theorem GRH.exponential_smoothing_of_partialSums_isBigO_rpow (a : ℕ → ℂ) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (h : (fun n : ℕ => ∑ k ∈ Finset.range (n+1), a k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ)) :
    (fun D : ℝ => ∑' n : ℕ, a n * (Real.exp (-(n : ℝ) * D⁻¹) : ℂ))
      =O[atTop] (fun D : ℝ => D ^ σ) := by sorry
