-- Prove2me | Theorems.Thm_OAI_Falconer_sphere_stationary_expansion
-- name    : OAI.Falconer.sphere_stationary_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:53:23.122895+00:00
-- url     : https://prove2.me/theorems/12e09e78-5430-412a-a943-2699c42b4d46
-- title:
--   OAI.Falconer.sphere_stationary_expansion: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.sphere_stationary_expansion` of [lean/OAI/MeasureTheory/Falconer/Angular/SphereStationary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Angular/SphereStationary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set`, `open scoped ContDiff`):
--
--   ```lean
--   theorem sphere_stationary_expansion
--       (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
--       (m J : ℕ) (hJ : 1 ≤ J) :
--       ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
--         ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
--         (∀ j ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3),
--           ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
--         ∀ Λ : ℝ, 1 ≤ Λ →
--         ‖((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*sphereOscillation Λ e (fun w => B w) -
--           (Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ B e +
--             star (Complex.exp (Complex.I*(Λ : ℂ))*
--               directStationarySum m J Λ (antipodalConjugate B) e))‖ ≤
--           A*Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.antipodalConjugate`, `OAI.Falconer.directStationarySum` and `OAI.Falconer.sphereOscillation` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedGnomonicSurface` and `OAI.Falconer.PublishedQuadraticStationary` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI.Falconer.exists_far_data_bound`, `OAI.Falconer.exists_rotated_masked_fourier_inverse_order` and `OAI.Falconer.exists_two_profile_masked_shell_order` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Angular/SphereStationary.lean (declaration OAI.Falconer.sphere_stationary_expansion)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set
open scoped ContDiff

theorem sphere_stationary_expansion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*sphereOscillation Λ e (fun w => B w) -
        (Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ B e +
          star (Complex.exp (Complex.I*(Λ : ℂ))*
            directStationarySum m J Λ (antipodalConjugate B) e))‖ ≤
        A*Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1) := by
  sorry

end Falconer

end OAI
end
