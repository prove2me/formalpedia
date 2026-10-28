-- Prove2me | Theorems.Thm_OAI_TuringRigidity_BoundedSetTheory_InternalCollapse_real_collapse_reconstructs
-- name    : OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.real_collapse_reconstructs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:34:28.535966+00:00
-- url     : https://prove2.me/theorems/46519a48-4ad2-408c-9dd2-feff102c16fe
-- title:
--   OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.real_collapse_reconstructs: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.real_collapse_reconstructs` of [lean/OAI/Computability/DegreeRigidity/Representation/RealCollapseReconstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/RealCollapseReconstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse`, with `open TransitiveNameModel CountableForcing AtomicForcing SetDegreeDecoding`, `open PersistentRestrictions`):
--
--   ```lean
--   theorem real_collapse_reconstructs (M : ZFSet.{u}) (hM : Transitive M)
--       (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
--       (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
--       {R c : ZFSet.{u}} (hRM : R ∈ M) (hcM : c ∈ M)
--       (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix R p) (hne : ∃ x, x ∈ R)
--       (hreal : ∀ x ∈ R, ∃ B : Oracle, SetModelReals.realSet B = x)
--       (I : CountableIdeal)
--       (hIR : ∀ d, d ∈ I.carrier ↔ ∃ B : Oracle, SetModelReals.realSet B ∈ R ∧ degree B = d)
--       (ρ : I ≃o I) (hρ : Persistent I ρ)
--       (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
--       (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
--       automorphismSet ρ ∈ genericExtensionSet M c G.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.OracleJump.jump`, `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal`, `OAI.TuringRigidity.SetDegreeDecoding.automorphismSet`, `OAI.TuringRigidity.SetModelReals.realSet`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.Infinity`, `OAI.TuringRigidity.BoundedSetTheory.Pairing`, `OAI.TuringRigidity.BoundedSetTheory.PowerSet` and `OAI.TuringRigidity.BoundedSetTheory.Union` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SigmaReplacement` and `OAI.TuringRigidity.BoundedSetTheory.SigmaSeparation` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.Prefix` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistentRestrictions.Persistent` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.persistent_modelIdeal_graph_mem_relativeModel` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/RealCollapseReconstruction.lean (declaration OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.real_collapse_reconstructs)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A002
import Definitions.Def_OAIQ064A003
import Definitions.Def_OAIQ064A004

section

attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing AtomicForcing SetDegreeDecoding
open PersistentRestrictions
universe u
attribute [local instance] order collapsePreorder

theorem real_collapse_reconstructs (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {R c : ZFSet.{u}} (hRM : R ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix R p) (hne : ∃ x, x ∈ R)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, SetModelReals.realSet B = x)
    (I : CountableIdeal)
    (hIR : ∀ d, d ∈ I.carrier ↔ ∃ B : Oracle, SetModelReals.realSet B ∈ R ∧ degree B = d)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    automorphismSet ρ ∈ genericExtensionSet M c G.carrier := by
  sorry

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end
