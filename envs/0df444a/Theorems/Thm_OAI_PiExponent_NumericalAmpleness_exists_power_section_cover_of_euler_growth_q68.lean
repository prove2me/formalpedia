-- Prove2me | Theorems.Thm_OAI_PiExponent_NumericalAmpleness_exists_power_section_cover_of_euler_growth_q68
-- name    : OAI.PiExponent.NumericalAmpleness.exists_power_section_cover_of_euler_growth_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:44:08.938694+00:00
-- url     : https://prove2.me/theorems/377f6aa5-4b77-455b-b836-6a036fb58b26
-- title:
--   OAI.PiExponent.NumericalAmpleness.exists_power_section_cover_of_euler_growth_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.NumericalAmpleness.exists_power_section_cover_of_euler_growth` of [lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiEffectivity.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiEffectivity.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.NumericalAmpleness`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Filter`, `open PiExponentSeshadri.Geometry`, `open PiExponent.SectionZeroIdeal`):
--
--   ```lean
--   theorem exists_power_section_cover_of_euler_growth_q68 [IsIntegral X]
--       (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
--       (hi : i ≫ PiExponent.polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
--       (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
--       (hdim : topologicalKrullDim X ≤ d+1)
--       (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
--         (L.pullback I.subschemeι).IsAmple)
--       (hgrowth : Tendsto (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) atTop atTop) :
--       ∃ a : ℕ, 0 < a ∧ ∃ k : ℕ, ∃ s : Fin k → GlobalSections X (L.pow a).sheaf,
--         (⨆ j, sectionOpen X (s j)) = ⊤
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.ProjectiveO1.projectiveSpace` and `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponent.polynomialProjectiveProjection` (definitions bundle `OAIQ068A001` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.pow` and `OAI.PiExponentSeshadri.Geometry.LineBundle.pullback` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.GlobalSections` and `OAI.PiExponentSeshadri.Geometry.sectionOpen` (definitions bundle `OAIQ068A013` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponentSeshadri.Geometry.eulerCharacteristic` (definitions bundle `OAIQ068A029` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.NumericalAmpleness.ample_slope_of_polynomial_pos_of_lower_criterion_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiEffectivity.lean (declaration OAI.PiExponent.NumericalAmpleness.exists_power_section_cover_of_euler_growth)

import Mathlib
import Definitions.Def_OAIQ068A029

section

attribute [-instance] _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Filter
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem exists_power_section_cover_of_euler_growth_q68 [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ PiExponent.polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) atTop atTop) :
    ∃ a : ℕ, 0 < a ∧ ∃ k : ℕ, ∃ s : Fin k → GlobalSections X (L.pow a).sheaf,
      (⨆ j, sectionOpen X (s j)) = ⊤ := by
  sorry

end
end PiExponent.NumericalAmpleness

end OAI
end
