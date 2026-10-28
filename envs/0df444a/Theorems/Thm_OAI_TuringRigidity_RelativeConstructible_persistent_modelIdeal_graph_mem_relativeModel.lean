-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_persistent_modelIdeal_graph_mem_relativeModel
-- name    : OAI.TuringRigidity.RelativeConstructible.persistent_modelIdeal_graph_mem_relativeModel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:53:34.357987+00:00
-- url     : https://prove2.me/theorems/4debf570-ed81-4596-9184-2582c7697005
-- title:
--   OAI.TuringRigidity.RelativeConstructible.persistent_modelIdeal_graph_mem_relativeModel: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.persistent_modelIdeal_graph_mem_relativeModel` of [lean/OAI/Computability/DegreeRigidity/Constructibility/RelativePersistentDescent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/RelativePersistentDescent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding`, `open PersistentRestrictions`):
--
--   ```lean
--   theorem persistent_modelIdeal_graph_mem_relativeModel (M : ZFSet.{u})
--       [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
--       (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT)
--       (hρ : Persistent (modelIdeal M hM hT) ρ) :
--       automorphismSet ρ ∈ relativeModel M (groundReals M)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.SetDegreeDecoding.automorphismSet`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive` and `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.RelativeConstructible.groundReals` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.PersistentRestrictions.Persistent` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.RelativeConstructible.relativeModel` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.ElementaryModel.modelIdeal` (definitions bundle `OAIQ064A008` of this split); `OAI.TuringRigidity.Degree` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.FullSetForcing.prescribed_one_real_names`, `OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one` and `OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/RelativePersistentDescent.lean (declaration OAI.TuringRigidity.RelativeConstructible.persistent_modelIdeal_graph_mem_relativeModel)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions
universe u

theorem persistent_modelIdeal_graph_mem_relativeModel (M : ZFSet.{u})
    [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT)
    (hρ : Persistent (modelIdeal M hM hT) ρ) :
    automorphismSet ρ ∈ relativeModel M (groundReals M) := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
