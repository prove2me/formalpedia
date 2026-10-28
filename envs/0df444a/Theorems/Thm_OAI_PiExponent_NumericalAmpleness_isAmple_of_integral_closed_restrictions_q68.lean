-- Prove2me | Theorems.Thm_OAI_PiExponent_NumericalAmpleness_isAmple_of_integral_closed_restrictions_q68
-- name    : OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:28:57.361513+00:00
-- url     : https://prove2.me/theorems/6addc583-052c-4142-9e37-d401c26df2b2
-- title:
--   OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions` of [lean/OAI/NumberTheory/PiExponent/Ampleness/IntegralComponentAmple.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/IntegralComponentAmple.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.NumericalAmpleness`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry`):
--
--   ```lean
--   theorem isAmple_of_integral_closed_restrictions_q68 [IsNoetherian X]
--       (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (L H : LineBundle X) (hH : H.IsAmple)
--       (hints : ∀ {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsClosedImmersion j],
--         (L.pullback j).IsAmple) : L.IsAmple
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.pullback` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.AdmissibleJetSurjectivity.blowupBundle_ample_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/IntegralComponentAmple.lean (declaration OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions)

import Mathlib
import Definitions.Def_OAIQ068A021

section

attribute [-instance] _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_integral_closed_restrictions_q68 [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (hints : ∀ {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsClosedImmersion j],
      (L.pullback j).IsAmple) : L.IsAmple := by
  sorry

end
end PiExponent.NumericalAmpleness

end OAI
end
