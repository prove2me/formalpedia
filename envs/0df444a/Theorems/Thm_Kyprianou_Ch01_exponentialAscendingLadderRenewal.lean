-- Prove2me | Theorems.Thm_Kyprianou_Ch01_exponentialAscendingLadderRenewal
-- name    : Kyprianou.Ch01.exponentialAscendingLadderRenewal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:22:49.766738+00:00
-- url     : https://prove2.me/theorems/3df498f1-f8a4-46dc-b189-46f03402f215
-- title:
--   Exercise 1.8(iv): exponential ascending ladder-height renewal measure
-- statement:
--   Exercise 1.8(iv), printed p. 30: if the ascending ladder-height increments are exponential with rate β>0, their renewal measure V=δ_0+Σ_{n≥1} μ^{*n} has V([0,x])=1+βx for x≥0, equivalently V(dy)=δ_0(dy)+β dy on the positive half-line. The draft builds the exponential law from its density and uses the pre-existing convolution-power definition, without assuming the renewal result.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.8(iv), printed p. 30.

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.exponentialAscendingLadderRenewal
    (beta : ℝ) (hbeta : 0 < beta) :
    let mu : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal
          (beta * Real.exp (-beta * x)))
    ∀ x : ℝ, 0 ≤ x →
      (∑' n : ℕ,
        ((QueueingFundamentals.MG1.convPow mu n)
          (Set.Icc (0 : ℝ) x)).toReal) = 1 + beta * x := by
  sorry
