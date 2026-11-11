-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_section_bound_of_curve_bound_s01
-- name    : OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:02:37.058688+00:00
-- url     : https://prove2.me/theorems/8d553528-44ad-4948-8b47-e57a194ee726
-- title:
--   OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound` of [lean/OAI/AlgebraicGeometry/Seshadri/Divisors/SectionCurveBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/SectionCurveBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini`):
--
--   ```lean
--   theorem section_bound_of_curve_bound_s01 (S : Surface) (L : LineBundle S.scheme)
--       (hL : L.IsAmple) {r : ℕ} (p : Configuration S r) (a : ℝ) (ha : 0 ≤ a)
--       (hC : ∀ C : IntegralCurve S,
--         a*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ))
--       (M : LineBundle S.scheme) (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0)
--       (U : Fin r → S.scheme.affineOpens)
--       (e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme)
--       (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
--         Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ)
--       (hρ : ∀ i, affineComplexPoint S.structureMap (U i) (ρ i) = p.val i)
--       (n : Fin r → ℕ)
--       (ho : ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i)) :
--       a*(∑ i, n i:ℕ) ≤ (mixedEuler S L M:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.affineComplexPoint` and `OAI.MaximalSeshadri.ProjectiveBertini.openScalars` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.affineCoefficient` and `OAI.MaximalSeshadri.Geometry.mixedEuler` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.ComplexPoint`, `OAI.MaximalSeshadri.Geometry.Configuration`, `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.complexBase`, `OAI.MaximalSeshadri.Geometry.curveDegree`, `OAI.MaximalSeshadri.Geometry.totalMultiplicity`, `OAI.MaximalSeshadri.Geometry.ComplexPoint.image` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.PointBlowup.effective_twist_bound_s01` and `OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/SectionCurveBound.lean (declaration OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem section_bound_of_curve_bound_s01 (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (p : Configuration S r) (a : ℝ) (ha : 0 ≤ a)
    (hC : ∀ C : IntegralCurve S,
      a*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ))
    (M : LineBundle S.scheme) (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0)
    (U : Fin r → S.scheme.affineOpens)
    (e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ)
    (hρ : ∀ i, affineComplexPoint S.structureMap (U i) (ρ i) = p.val i)
    (n : Fin r → ℕ)
    (ho : ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i)) :
    a*(∑ i, n i:ℕ) ≤ (mixedEuler S L M:ℝ) := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
