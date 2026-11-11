-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_curve_lower_of_homogeneous_section_test_s01
-- name    : OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:01:48.280262+00:00
-- url     : https://prove2.me/theorems/cf8de8a6-b53a-4e50-ae1d-7373f103db51
-- title:
--   OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test` of [lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/AllCurveLowerBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/AllCurveLowerBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini`):
--
--   ```lean
--   theorem curve_lower_of_homogeneous_section_test_s01 (S : Surface)
--       (L : LineBundle S.scheme) (hL : L.IsAmple) {r : ℕ} (hr : 0 < r)
--       (p : Configuration S r) (U : S.scheme.affineOpens)
--       (eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
--       (htest : ∀ k m : ℕ, 0 < k → 0 < m →
--         (k:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (m:ℝ) →
--         ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
--             Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
--           (∀ i, affineComplexPoint S.structureMap U (ρ i) = p.val i) ∧
--           ∀ s : O S.scheme ⟶ (L.pow k).sheaf,
--             (∀ i, affineCoefficient U (localPowerFrame U.1 eL k) s ∈
--               (RingHom.ker (ρ i))^m) → s = 0)
--       (C : IntegralCurve S) :
--       Real.sqrt ((selfIntersection S L:ℝ)/r) * (totalMultiplicity S r C p:ℝ) ≤
--         (curveDegree S L C:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.affineComplexPoint` and `OAI.MaximalSeshadri.ProjectiveBertini.openScalars` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.localPowerFrame` and `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.affineCoefficient` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.ComplexPoint`, `OAI.MaximalSeshadri.Geometry.Configuration`, `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.complexBase`, `OAI.MaximalSeshadri.Geometry.curveDegree`, `OAI.MaximalSeshadri.Geometry.modulePow`, `OAI.MaximalSeshadri.Geometry.selfIntersection`, `OAI.MaximalSeshadri.Geometry.totalMultiplicity`, `OAI.MaximalSeshadri.Geometry.ComplexPoint.image` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/AllCurveLowerBound.lean (declaration OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem curve_lower_of_homogeneous_section_test_s01 (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) {r : ℕ} (hr : 0 < r)
    (p : Configuration S r) (U : S.scheme.affineOpens)
    (eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (htest : ∀ k m : ℕ, 0 < k → 0 < m →
      (k:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (m:ℝ) →
      ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
          Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
        (∀ i, affineComplexPoint S.structureMap U (ρ i) = p.val i) ∧
        ∀ s : O S.scheme ⟶ (L.pow k).sheaf,
          (∀ i, affineCoefficient U (localPowerFrame U.1 eL k) s ∈
            (RingHom.ker (ρ i))^m) → s = 0)
    (C : IntegralCurve S) :
    Real.sqrt ((selfIntersection S L:ℝ)/r) * (totalMultiplicity S r C p:ℝ) ≤
      (curveDegree S L C:ℝ) := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
