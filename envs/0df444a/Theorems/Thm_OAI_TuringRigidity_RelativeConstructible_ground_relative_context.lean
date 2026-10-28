-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_ground_relative_context
-- name    : OAI.TuringRigidity.RelativeConstructible.ground_relative_context
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:44:56.544181+00:00
-- url     : https://prove2.me/theorems/825ef489-ddf2-4465-8229-a4c18962c428
-- title:
--   OAI.TuringRigidity.RelativeConstructible.ground_relative_context: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.ground_relative_context` of [lean/OAI/Computability/DegreeRigidity/Constructibility/RelativeDefCertificates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/RelativeDefCertificates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding`, `open BoundedDefinability SetModelFunctions`):
--
--   ```lean
--   theorem ground_relative_context (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
--       Context (relativeModel M (groundReals M))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.RelativeConstructible.groundReals` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.RelativeConstructible.relativeModel` and `OAI.TuringRigidity.SetModelFunctions.Context` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.OrdinalArithmetic.omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalArithmetic.relative_omega_power_internal`, `OAI.TuringRigidity.OrdinalArithmetic.uniform_omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalCoding.vectorCode_certificates_at_levels`, `OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition`, `OAI.TuringRigidity.RelativeConstructible.hierarchy_checked_at_levels` and `OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/RelativeDefCertificates.lean (declaration OAI.TuringRigidity.RelativeConstructible.ground_relative_context)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem ground_relative_context (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    Context (relativeModel M (groundReals M)) := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
