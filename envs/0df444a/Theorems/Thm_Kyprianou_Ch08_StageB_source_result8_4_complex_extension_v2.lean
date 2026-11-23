-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_4_complex_extension_v2
-- name    : Kyprianou.Ch08.StageB.source_result8_4_complex_extension_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T14:20:51.710796+00:00
-- url     : https://prove2.me/theorems/525054e5-1fbd-45d0-a758-133b5f537d89
-- title:
--   Lemma 8.4 source child: entire scale certificate
-- statement:
--   The exact final existential clause of sourceCertificate_result8_4, retaining every outer source binder and hypothesis. Lemma 8.3 supplies an entire extension F of the real scale family; defining G(z,x)=exp(−cx)F(z+ψ(c),x) gives the required real tiltedScale values and the complex identity on the stated domains.
-- source:
--   Exact final existential conjunction of Kyprianou.Ch08.StageB.sourceCertificate_result8_4, from Kyprianou (2006), Chapter 8, Lemma 8.4, physical PDF p. 230. The complete F/G interface, every quantifier and every domain guard are retained; the only imported mathematical prerequisite is the already Proved source result 8.3.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_3_v2
set_option autoImplicit false
open MeasureTheory
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

namespace Kyprianou.Ch08.StageB

theorem source_result8_4_complex_extension_v2
    (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [hP : IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (c : ℝ)
    (hc : Integrable (fun ω => Real.exp (c * D.X 1 ω)) P) :
    ∃ (F G : ℂ → ℝ → ℂ),
      (∀ x : ℝ, 0 ≤ x →
        Differentiable ℂ (fun q : ℂ => F q x) ∧
        Differentiable ℂ (fun q : ℂ => G q x)) ∧
      (∀ (q x : ℝ), 0 ≤ q → 0 ≤ x →
        F (q : ℂ) x = (W q x : ℂ)) ∧
      (∀ (p x : ℝ), 0 ≤ p → 0 ≤ x →
        0 ≤ p + ψ c →
        G (p : ℂ) x =
          ((tiltedScale c (W (p + ψ c)) x) : ℂ)) ∧
      (∀ (q : ℂ) (x : ℝ), 0 ≤ x →
        F q x =
          Complex.exp (((c * x : ℝ) : ℂ)) *
            G (q - ((ψ c : ℝ) : ℂ)) x) := by
  sorry

end Kyprianou.Ch08.StageB
