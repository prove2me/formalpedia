-- Prove2me | Theorems.Thm_OAI_TuringRigidity_FullSetForcing_prescribed_one_real_names
-- name    : OAI.TuringRigidity.FullSetForcing.prescribed_one_real_names
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:48:57.23788+00:00
-- url     : https://prove2.me/theorems/5217e80a-fdd4-4d54-9627-731218ace971
-- title:
--   OAI.TuringRigidity.FullSetForcing.prescribed_one_real_names: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.FullSetForcing.prescribed_one_real_names` of [lean/OAI/Computability/DegreeRigidity/Representation/PrescribedOneRealNames.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/PrescribedOneRealNames.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.FullSetForcing`, with `open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding`, `open PersistentRestrictions RecursiveNames CountableForcing AtomicForcing RelativeConstructible ArithmeticTree`):
--
--   ```lean
--   theorem prescribed_one_real_names (π : Degree ≃o Degree)
--       (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
--       (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
--         π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
--       {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
--       (hc : c ∈ M) (ho : o ∈ M)
--       (hos : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
--       (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (ht : ⊤ ∈ G.carrier)
--       (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ) :
--       let E := genericExtensionSet M c G.carrier
--       let hE := genericExtensionSet_transitive M c hM G.carrier
--       let hTE := extension_sourceT M hM hT hc ho hos G hG ht
--       let J := modelIdeal E hE hTE
--       ∃ hIJ : (modelIdeal M hM hT).carrier ⊆ J.carrier, ∃ σ : J ≃o J,
--         RestrictsTo π J σ ∧ Extends hIJ ρ σ ∧ SetGenericallyPersistent E J σ ∧
--         ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
--           δ.toZFSet ∈ M ∧ P ∈ modelReals E ∧ p.bound ≤ 2 ∧
--           realCode P ∈ level (groundReals E) δ ∧
--           automorphismSet σ = definedSubset (level (groundReals E) δ) p
--             (fun _ : Fin p.bound => realCode P) ∧
--           ∃ f a : Name (Conditions c),
--             f.encode (label c) ∈ M ∧ a.encode (label c) ∈ M ∧
--             f.val G.carrier = automorphismSet σ ∧ a.val G.carrier = realCode P
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.instSemilatticeSupDegree`, `OAI.TuringRigidity.ArithmeticTree.SetGenericallyPersistent`, `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.OracleJump.jump`, `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal`, `OAI.TuringRigidity.RecursiveNames.Name`, `OAI.TuringRigidity.SetDegreeDecoding.automorphismSet`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.TransitiveNameModel.label`, `OAI.TuringRigidity.RecursiveNames.Name.encode` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.ElementaryModel.SentenceForm`, `OAI.TuringRigidity.RelativeConstructible.groundReals` and `OAI.TuringRigidity.ElementaryModel.SentenceForm.bound` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT`, `OAI.TuringRigidity.BoundedSetTheory.realCode` and `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet_transitive` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistentRestrictions.Extends` and `OAI.TuringRigidity.PersistentRestrictions.RestrictsTo` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.BoundedSetTheory.modelReals` and `OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RelativeConstructible.definedSubset` and `OAI.TuringRigidity.RelativeConstructible.level` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.BoundedSetTheory.extension_sourceT` and `OAI.TuringRigidity.ElementaryModel.modelIdeal` (definitions bundle `OAIQ064A008` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/PrescribedOneRealNames.lean (declaration OAI.TuringRigidity.FullSetForcing.prescribed_one_real_names)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

section

attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FullSetForcing
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions RecursiveNames CountableForcing AtomicForcing RelativeConstructible ArithmeticTree
universe u

theorem prescribed_one_real_names (π : Degree ≃o Degree)
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (ho : o ∈ M)
    (hos : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (ht : ⊤ ∈ G.carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc ho hos G hG ht
    let J := modelIdeal E hE hTE
    ∃ hIJ : (modelIdeal M hM hT).carrier ⊆ J.carrier, ∃ σ : J ≃o J,
      RestrictsTo π J σ ∧ Extends hIJ ρ σ ∧ SetGenericallyPersistent E J σ ∧
      ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
        δ.toZFSet ∈ M ∧ P ∈ modelReals E ∧ p.bound ≤ 2 ∧
        realCode P ∈ level (groundReals E) δ ∧
        automorphismSet σ = definedSubset (level (groundReals E) δ) p
          (fun _ : Fin p.bound => realCode P) ∧
        ∃ f a : Name (Conditions c),
          f.encode (label c) ∈ M ∧ a.encode (label c) ∈ M ∧
          f.val G.carrier = automorphismSet σ ∧ a.val G.carrier = realCode P := by
  sorry

end TuringRigidity.FullSetForcing

end OAI
end
