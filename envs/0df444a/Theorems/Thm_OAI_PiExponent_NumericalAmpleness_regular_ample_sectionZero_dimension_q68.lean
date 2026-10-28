-- Prove2me | Theorems.Thm_OAI_PiExponent_NumericalAmpleness_regular_ample_sectionZero_dimension_q68
-- name    : OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:43:56.498996+00:00
-- url     : https://prove2.me/theorems/f7461fa4-a048-4bd2-a992-290594c5f66b
-- title:
--   OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension` of [lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleDivisorDimension.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleDivisorDimension.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.NumericalAmpleness`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens`, `open PiExponent.SectionZeroIdeal`):
--
--   ```lean
--   theorem regular_ample_sectionZero_dimension_q68
--       [IsNoetherian X] [Nonempty X]
--       (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (H : LineBundle X) (hH : H.IsAmple)
--       (s : GlobalSections X H.sheaf) [Mono s] (d : ℕ)
--       (hdim : topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞)) :
--       Nonempty (zeroIdeal H s).subscheme ∧
--         topologicalKrullDim (zeroIdeal H s).subscheme = d
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` and `OAI.PiExponentSeshadri.Geometry.structureSheaf` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.GlobalSections` (definitions bundle `OAIQ068A013` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponent.SectionZeroIdeal.zeroIdeal` (definitions bundle `OAIQ068A029` of this split).
--
--   **Used by.** The proofs of `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_pos_of_ample_q68` and `OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin_q68` of this split import it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleDivisorDimension.lean (declaration OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension)

import Mathlib
import Definitions.Def_OAIQ068A029

section

attribute [-instance] _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
open PiExponent.SectionZeroIdeal

variable {X Y : Scheme.{0}}

theorem regular_ample_sectionZero_dimension_q68
    [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (s : GlobalSections X H.sheaf) [Mono s] (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞)) :
    Nonempty (zeroIdeal H s).subscheme ∧
      topologicalKrullDim (zeroIdeal H s).subscheme = d := by
  sorry

end
end PiExponent.NumericalAmpleness

end OAI
end
