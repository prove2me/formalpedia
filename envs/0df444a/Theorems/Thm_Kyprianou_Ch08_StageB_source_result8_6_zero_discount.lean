-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:13:00.40915+00:00
-- url     : https://prove2.me/theorems/96dc98bb-5b2d-4b59-bcd6-ec8506f21f5e
-- title:
--   Source scale-function boundary value and bounded-variation dichotomy at zero discount
-- statement:
--   Exact Kyprianou (2006) Lemma 8.6 source process dichotomy at q=0: W0(0)=0 iff unbounded variation, and for bounded variation drift d>0 and W0(0)=1/d. All original stochastic process, Laplace-exponent and scale-family hypotheses are retained. Together with proved source q-origin discount invariance, this supplies the full original q≥0 statement.
-- source:
--   Kyprianou (2006) Lemma 8.6, printed p.222, exactly original source process and triplet.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory

namespace Kyprianou.Ch08.StageB

theorem source_result8_6_zero_discount :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ((W 0 0 = 0) ↔
        ¬ HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure) ∧
      (HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure →
        0 < bvDrift D.triplet.drift D.triplet.levyMeasure ∧
        W 0 0 = (bvDrift D.triplet.drift D.triplet.levyMeasure)⁻¹) := by
  sorry

end Kyprianou.Ch08.StageB
