-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleJetSurjectivity_blowupBundle_ample_q68
-- name    : OAI.PiExponent.AdmissibleJetSurjectivity.blowupBundle_ample_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:44:46.393417+00:00
-- url     : https://prove2.me/theorems/f06f292b-0ac2-46fb-a00c-55a00f80dc36
-- title:
--   OAI.PiExponent.AdmissibleJetSurjectivity.blowupBundle_ample_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.AdmissibleJetSurjectivity.blowupBundle_ample` of [lean/OAI/NumberTheory/PiExponent/Ampleness/AdmissibleJetAmpleness.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/AdmissibleJetAmpleness.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.AdmissibleJetSurjectivity`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry`, `open PiExponent.AdmissibleBlowupGeometry PiExponent.BlowupJetSurjectivity`):
--
--   ```lean
--   theorem blowupBundle_ample_q68 :
--       (blowupBundle (centerIdeal d) (hyperplane d)).IsAmple
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.AdmissibleParameters` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponent.AdmissibleBlowupGeometry.compactification` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponent.AdmissibleBlowupGeometry.centerIdeal`, `OAI.PiExponent.AdmissibleBlowupGeometry.hyperplane` and `OAI.PiExponentSeshadri.BlowupGluing.scheme` (definitions bundle `OAIQ068A020` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponent.BlowupJetSurjectivity.blowupBundle` (definitions bundle `OAIQ068A038` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.main` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/AdmissibleJetAmpleness.lean (declaration OAI.PiExponent.AdmissibleJetSurjectivity.blowupBundle_ample)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A038

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AdmissibleJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.AdmissibleBlowupGeometry PiExponent.BlowupJetSurjectivity
attribute [local irreducible] AdmissibleBlowupGeometry.centerIdeal
  AdmissibleBlowupGeometry.hyperplane
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem blowupBundle_ample_q68 :
    (blowupBundle (centerIdeal d) (hyperplane d)).IsAmple := by
  sorry

end
end PiExponent.AdmissibleJetSurjectivity

end OAI
end
