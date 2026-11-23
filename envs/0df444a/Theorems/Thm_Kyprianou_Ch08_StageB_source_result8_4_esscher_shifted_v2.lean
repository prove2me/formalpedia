-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_4_esscher_shifted_v2
-- name    : Kyprianou.Ch08.StageB.source_result8_4_esscher_shifted_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:20:45.936221+00:00
-- url     : https://prove2.me/theorems/c7acd269-7433-4157-91de-87806fb949a6
-- title:
--   Lemma 8.4 source child: real Esscher Laplace exponent shift
-- statement:
--   The exact real-parameter Esscher Laplace shift clause of sourceCertificate_result8_4, retaining every outer source binder and hypothesis. For β ≥ 0, t > 0 and the stated integrability of exp((c+β)X_t), the expectation against the Esscher density equals exp(t(ψ(c+β)−ψ(c))). The real tilt c is unrestricted; negative c remains eligible when its stated moment exists.
-- source:
--   Exact second conjunction of Kyprianou.Ch08.StageB.sourceCertificate_result8_4, from Kyprianou (2006), Chapter 8, Lemma 8.4, physical PDF p. 230. The source's binders, assumptions, time domain, β domain, integrability premise and conclusion are retained.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

namespace Kyprianou.Ch08.StageB

theorem source_result8_4_esscher_shifted_v2
    (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [hP : IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (c : ℝ)
    (hc : Integrable (fun ω => Real.exp (c * D.X 1 ω)) P) :
    IsEsscherLaplaceShifted P D ψ c := by
  sorry

end Kyprianou.Ch08.StageB
