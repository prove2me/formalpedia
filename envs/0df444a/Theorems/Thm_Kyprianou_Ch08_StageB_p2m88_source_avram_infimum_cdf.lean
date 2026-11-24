-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_avram_infimum_cdf
-- name    : Kyprianou.Ch08.StageB.p2m88_source_avram_infimum_cdf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:48:06.102343+00:00
-- url     : https://prove2.me/theorems/81b3aeb7-60d1-4c9e-bd99-2b120971f6c9
-- title:
--   Transfer the proved one-sided exit formula to the actual infimum CDF
-- statement:
--   For an Avram path model agreeing with the source model almost surely at all times, the negative-infimum clock CDF equals q/phi times the source scale function less q times its primitive at every nonnegative argument.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7, Wiener–Hopf decomposition at the exponential time.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Transfer the proved one-sided exit formula to the actual infimum CDF -/
theorem p2m88_source_avram_infimum_cdf :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (F : Filtration ℝ≥0 mΩ)
        (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      (∀ᵐ ω ∂P, ∀ t, X.X t ω = D.X t ω) →
      ∀ q : ℝ, 0 < q → ∀ b : ℝ, 0 ≤ b →
      cdf ((P.prod (expMeasure q)).map
        (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1})) b =
        q / Phi ψ q * W q b - q * ∫ s in (0 : ℝ)..b, W q s := by
  sorry

end Kyprianou.Ch08.StageB
