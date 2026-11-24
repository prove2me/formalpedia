-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_height_intersection_payoff
-- name    : Kyprianou.Ch08.StageB.p2m810_height_intersection_payoff
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:44:10.070151+00:00
-- url     : https://prove2.me/theorems/b009583b-8235-484e-aa3b-12e725ce8310
-- title:
--   Intersection of descending strict height bounds equals the strict survival payoff
-- statement:
--   On a finite upper clock the reflected height at the record is zero. The descending strict bounds intersect to the weak pre-record bound, which is equivalent to strict record survival; infinite upper clocks have zero payoff.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); actual height law of Theorem 8.2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Intersection of descending strict height bounds equals the strict survival payoff -/
theorem p2m810_height_intersection_payoff :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q a l : ℝ), 0 ≤ q → 0 < a → 0 < l →
      (fun ω => (⋂ k : ℕ, {ω | NoDrawdownBeforeUpcrossing D.X l
          (a+1/((k:ℝ)+1)) ω}).indicator (fun ω => discountedAt q (tauPlus D.X l ω)) ω)
        =ᵐ[P] (fun ω => if tauPlus D.X l ω < reflectedSupExit D.X 0 a ω
          then discountedAt q (tauPlus D.X l ω) else 0) := by
  sorry
end Kyprianou.Ch08.StageB
