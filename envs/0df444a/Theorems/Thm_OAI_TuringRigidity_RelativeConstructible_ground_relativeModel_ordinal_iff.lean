-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_ground_relativeModel_ordinal_iff
-- name    : OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:45:19.73429+00:00
-- url     : https://prove2.me/theorems/12ee6fd2-4614-4fb5-9c3e-b5ca274e8a69
-- title:
--   OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff` of [lean/OAI/Computability/DegreeRigidity/Constructibility/RelativeModelOrdinals.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/RelativeModelOrdinals.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open BoundedSetTheory TransitiveNameModel InternalRank`):
--
--   ```lean
--   theorem ground_relativeModel_ordinal_iff (M : ZFSet.{u}) (hM : Transitive M)
--       (hT : SourceT M) (o : Ordinal.{u}) :
--       o.toZFSet ∈ relativeModel M (groundReals M) ↔ o.toZFSet ∈ M
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.RelativeConstructible.groundReals` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.RelativeConstructible.relativeModel` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.OrdinalArithmetic.omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalArithmetic.relative_omega_power_internal`, `OAI.TuringRigidity.OrdinalArithmetic.uniform_omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalCoding.vectorCode_certificates_at_levels` and `OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/RelativeModelOrdinals.lean (declaration OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff)

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
open BoundedSetTheory TransitiveNameModel InternalRank
universe u

theorem ground_relativeModel_ordinal_iff (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (o : Ordinal.{u}) :
    o.toZFSet ∈ relativeModel M (groundReals M) ↔ o.toZFSet ∈ M := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
