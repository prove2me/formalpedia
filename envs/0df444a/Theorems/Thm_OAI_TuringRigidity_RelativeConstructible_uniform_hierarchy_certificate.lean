-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_uniform_hierarchy_certificate
-- name    : OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:47:15.544023+00:00
-- url     : https://prove2.me/theorems/2a237cf3-ad4e-4b5a-9602-ab4a12e6aa6e
-- title:
--   OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate` of [lean/OAI/Computability/DegreeRigidity/Constructibility/HierarchySyntax.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/HierarchySyntax.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding`, `open BoundedDefinability SetModelFunctions`):
--
--   ```lean
--   theorem uniform_hierarchy_certificate (M R d q : ZFSet.{u}) (hM : Transitive M)
--       (hT : SourceT M) (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M)
--       (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) :
--       ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
--         ∀ x ∈ d, ∀ f ∈ M, p.Realize M (cons f (cons x a)) ↔
--           ∃ r ∈ M, HierarchyGraph M (seed R) (hull d q x) r f
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.BoundedSetTheory.cons` and `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.RelativeConstructible.seed` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula`, `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.Realize` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.BoundedSetTheory.hull` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.RelativeConstructible.HierarchyGraph` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.OrdinalArithmetic.omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalArithmetic.relative_omega_power_internal`, `OAI.TuringRigidity.OrdinalArithmetic.uniform_omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalCoding.vectorCode_certificates_at_levels`, `OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level`, `OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition`, `OAI.TuringRigidity.RelativeConstructible.ground_idealSet_mem_relativeModel`, `OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff`, `OAI.TuringRigidity.RelativeConstructible.ground_relative_context`, `OAI.TuringRigidity.RelativeConstructible.hierarchy_checked_at_levels`, `OAI.TuringRigidity.RelativeConstructible.persistent_modelIdeal_graph_mem_relativeModel`, `OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension`, `OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels` and `OAI.TuringRigidity.RelativeConstructible.uniform_ordinal_definition_symmetric` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/HierarchySyntax.lean (declaration OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate)

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

theorem uniform_hierarchy_certificate (M R d q : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M)
    (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) :
    ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
      ∀ x ∈ d, ∀ f ∈ M, p.Realize M (cons f (cons x a)) ↔
        ∃ r ∈ M, HierarchyGraph M (seed R) (hull d q x) r f := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
