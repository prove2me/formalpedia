-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_hierarchyGraph_sigmaDefinable
-- name    : OAI.TuringRigidity.RelativeConstructible.hierarchyGraph_sigmaDefinable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:44:57.428412+00:00
-- url     : https://prove2.me/theorems/b5f8b9e0-cbb5-4162-8707-e48f1e4077e7
-- title:
--   OAI.TuringRigidity.RelativeConstructible.hierarchyGraph_sigmaDefinable: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.hierarchyGraph_sigmaDefinable` of [lean/OAI/Computability/DegreeRigidity/Constructibility/HierarchySyntax.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/HierarchySyntax.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding`, `open BoundedDefinability SetModelFunctions`):
--
--   ```lean
--   theorem hierarchyGraph_sigmaDefinable (hM : Transitive M) (hT : SourceT M) (s d r f : ℕ) :
--       SigmaDefinable M (fun e => HierarchyGraph M (e s) (e d) (e r) (e f))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedDefinability.SigmaDefinable` and `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.RelativeConstructible.HierarchyGraph` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.OrdinalArithmetic.omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalArithmetic.relative_omega_power_internal`, `OAI.TuringRigidity.OrdinalArithmetic.uniform_omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalCoding.vectorCode_certificates_at_levels`, `OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level`, `OAI.TuringRigidity.RelativeConstructible.ground_idealSet_mem_relativeModel`, `OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff`, `OAI.TuringRigidity.RelativeConstructible.ground_relative_context`, `OAI.TuringRigidity.RelativeConstructible.hierarchy_checked_at_levels`, `OAI.TuringRigidity.RelativeConstructible.persistent_modelIdeal_graph_mem_relativeModel`, `OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels` and `OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/HierarchySyntax.lean (declaration OAI.TuringRigidity.RelativeConstructible.hierarchyGraph_sigmaDefinable)

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
variable {M : ZFSet.{u}}

theorem hierarchyGraph_sigmaDefinable (hM : Transitive M) (hT : SourceT M) (s d r f : ℕ) :
    SigmaDefinable M (fun e => HierarchyGraph M (e s) (e d) (e r) (e f)) := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
