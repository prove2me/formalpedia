-- Prove2me | Theorems.Thm_OAI_PiExponentSeshadri_ComponentAmpleDescent_isAmple_of_reduced_closed_cover_q68
-- name    : OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:33:07.941545+00:00
-- url     : https://prove2.me/theorems/ee76b09c-9a50-4bae-b7d6-3b686c036e5f
-- title:
--   OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover` of [lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescent.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescent.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentSeshadri.ComponentAmpleDescent`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace`, `open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule`):
--
--   ```lean
--   theorem isAmple_of_reduced_closed_cover_q68
--       (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
--       (L H : LineBundle X) (hH : H.IsAmple)
--       (I J : X.IdealSheafData) (hcover : I.support ⊔ J.support = ⊤)
--       (hI : (L.pullback I.subschemeι).IsAmple) (hJ : (L.pullback J.subschemeι).IsAmple) :
--       L.IsAmple
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.pullback` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescent.lean (declaration OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover)

import Mathlib
import Definitions.Def_OAIQ068A021

section

attribute [-instance] _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]
variable {R : Type} [CommRing R] [IsNoetherianRing R]

theorem isAmple_of_reduced_closed_cover_q68
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (I J : X.IdealSheafData) (hcover : I.support ⊔ J.support = ⊤)
    (hI : (L.pullback I.subschemeι).IsAmple) (hJ : (L.pullback J.subschemeι).IsAmple) :
    L.IsAmple := by
  sorry

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end
