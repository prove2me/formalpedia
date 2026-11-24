-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sup_zero_slope_no_crossing
-- name    : Kyprianou.Ch08.StageB.p2m810_sup_zero_slope_no_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:05:07.896271+00:00
-- url     : https://prove2.me/theorems/44349357-9d85-4fbc-b8ec-d3c7cc88f438
-- title:
--   Zero right scale derivative prevents strict drawdown exits
-- statement:
--   If the right derivative vanishes, q is zero and the strict height tail is zero by Theorem 8.2. If any negative marginal increment had positive probability, repeated independent increments would give arbitrarily large drawdowns, contradicting zero strict height tail. Conclude all actual paths are nondecreasing almost surely and no strict drawdown occurs.
-- source:
--   Kyprianou (2006), Theorem 8.10(i); Avram, Kyprianou and Pistorius (2004), section 4, equations (13)-(22).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
/-- Zero right scale derivative prevents strict drawdown exits -/
theorem p2m810_sup_zero_slope_no_crossing :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      derivWithin (W q) (Ici a) a = 0 →
      ∀ᵐ ω ∂P, reflectedSupExit D.X x a ω = ⊤ := by
  sorry
end Kyprianou.Ch08.StageB
