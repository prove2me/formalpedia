-- Prove2me | Theorems.Thm_OAI_PiExponentSeshadri_ComponentAmpleDescent_eventual_tensor_cohomology_zero_of_closed_pushforward_q68
-- name    : OAI.PiExponentSeshadri.ComponentAmpleDescent.eventual_tensor_cohomology_zero_of_closed_pushforward_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:44:16.252021+00:00
-- url     : https://prove2.me/theorems/d6ea3801-3388-4f32-9c8a-c44414477f4d
-- title:
--   OAI.PiExponentSeshadri.ComponentAmpleDescent.eventual_tensor_cohomology_zero_of_closed_pushforward_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentSeshadri.ComponentAmpleDescent.eventual_tensor_cohomology_zero_of_closed_pushforward` of [lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentSupported.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentSupported.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentSeshadri.ComponentAmpleDescent`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian`, `open PiExponentSeshadri.Geometry`):
--
--   ```lean
--   theorem eventual_tensor_cohomology_zero_of_closed_pushforward_q68
--       (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
--       (f : Y ⟶ X) [IsClosedImmersion f]
--       (M : X.Modules) (N : Y.Modules) [N.IsFinitePresentation]
--       (e : (Scheme.Modules.pushforward f).obj N ≅ M)
--       (K L : LineBundle X) (hL : (L.pullback f).IsAmple) :
--       ∃ B : ℕ, ∀ n ≥ B, ∀ q, 0 < q →
--         ∀ x : cohomology (moduleTensor X M (K.tensor (L.pow n)).sheaf) q, x = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle`, `OAI.PiExponentSeshadri.Geometry.moduleTensor` and `OAI.PiExponentSeshadri.Geometry.structureSheaf` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.schemeHasExt` (definitions bundle `OAIQ068A003` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.pow` and `OAI.PiExponentSeshadri.Geometry.LineBundle.pullback` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponentSeshadri.Geometry.cohomology` (definitions bundle `OAIQ068A022` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.tensor` (definitions bundle `OAIQ068A028` of this split).
--
--   **Used by.** The proof of `OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentSupported.lean (declaration OAI.PiExponentSeshadri.ComponentAmpleDescent.eventual_tensor_cohomology_zero_of_closed_pushforward)

import Mathlib
import Definitions.Def_OAIQ068A028

section

attribute [-instance] _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_tensor_cohomology_zero_of_closed_pushforward_q68
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (f : Y ⟶ X) [IsClosedImmersion f]
    (M : X.Modules) (N : Y.Modules) [N.IsFinitePresentation]
    (e : (Scheme.Modules.pushforward f).obj N ≅ M)
    (K L : LineBundle X) (hL : (L.pullback f).IsAmple) :
    ∃ B : ℕ, ∀ n ≥ B, ∀ q, 0 < q →
      ∀ x : cohomology (moduleTensor X M (K.tensor (L.pow n)).sheaf) q, x = 0 := by
  sorry

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end
