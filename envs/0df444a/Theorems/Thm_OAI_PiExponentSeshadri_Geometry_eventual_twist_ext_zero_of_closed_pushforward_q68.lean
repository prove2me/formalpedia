-- Prove2me | Theorems.Thm_OAI_PiExponentSeshadri_Geometry_eventual_twist_ext_zero_of_closed_pushforward_q68
-- name    : OAI.PiExponentSeshadri.Geometry.eventual_twist_ext_zero_of_closed_pushforward_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:32:17.335979+00:00
-- url     : https://prove2.me/theorems/0192d28d-ef27-48ae-a956-9b38e520a197
-- title:
--   OAI.PiExponentSeshadri.Geometry.eventual_twist_ext_zero_of_closed_pushforward_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentSeshadri.Geometry.eventual_twist_ext_zero_of_closed_pushforward` of [lean/OAI/NumberTheory/PiExponent/Approximation/ClosedSupportedSerre.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/ClosedSupportedSerre.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian`):
--
--   ```lean
--   theorem eventual_twist_ext_zero_of_closed_pushforward_q68
--       {R : Type} [CommRing R] [IsNoetherianRing R]
--       (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
--       (i : Y ⟶ X) [IsClosedImmersion i]
--       (L : LineBundle X) (hL : (L.pullback i).IsAmple)
--       (M : X.Modules) (N : Y.Modules) [N.IsFinitePresentation]
--       (e : M ≅ (Scheme.Modules.pushforward i).obj N) :
--       ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
--         ∀ x : Abelian.Ext.{1} (structureSheaf X) ((moduleTwistFunctor L n).obj M) q, x = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` and `OAI.PiExponentSeshadri.Geometry.structureSheaf` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.instHasExtModules_solutions` (definitions bundle `OAIQ068A011` of this split); `OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor` and `OAI.PiExponentSeshadri.Geometry.LineBundle.pullback` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/ClosedSupportedSerre.lean (declaration OAI.PiExponentSeshadri.Geometry.eventual_twist_ext_zero_of_closed_pushforward)

import Mathlib
import Definitions.Def_OAIQ068A011
import Definitions.Def_OAIQ068A021

section

attribute [-instance] _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {X Y : Scheme.{0}}

local instance localInst_r5c5ba2_1 (Z : Scheme.{0}) : HasExt.{1} Z.Modules := HasExt.standard _
theorem eventual_twist_ext_zero_of_closed_pushforward_q68
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (i : Y ⟶ X) [IsClosedImmersion i]
    (L : LineBundle X) (hL : (L.pullback i).IsAmple)
    (M : X.Modules) (N : Y.Modules) [N.IsFinitePresentation]
    (e : M ≅ (Scheme.Modules.pushforward i).obj N) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X) ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  sorry

end
end PiExponentSeshadri.Geometry

end OAI
end
