-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_prescribed_real_hull_extension
-- name    : OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:52:31.184987+00:00
-- url     : https://prove2.me/theorems/8f1e8a3b-3062-4626-940e-d1c29f41ea62
-- title:
--   OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension` of [lean/OAI/Computability/DegreeRigidity/Representation/PrescribedRealHullExtension.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/PrescribedRealHullExtension.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing BoundedForcing`, `open CohenGroundPoset InternalCountableOrdinals ElementaryModel SetDegreeDecoding PersistentRestrictions`, `open FullSetForcing OriginalRealDefinitionTransport`):
--
--   ```lean
--   theorem prescribed_real_hull_extension (π : Degree ≃o Degree)
--       (M K : ZFSet.{0}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
--       (hK : FirstUncountable M K)
--       (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
--         π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
--       (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ)
--       (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
--       (hG : GroundGeneric M G) :
--       let c := conditions (ZFSet.prod K ZFSet.omega)
--       let E := genericExtensionSet M c G.carrier
--       let hE := genericExtensionSet_transitive M c hM G.carrier
--       let hTE := extension_sourceT M hM hT (manyColumn_internal M K hM hT hK.2.1).1
--         (manyColumn_internal M K hM hT hK.2.1).2 (InternalCollapse.orderSet_pair c)
--           G hG (G.upper le_top G.nonempty.choose_spec)
--       let I := modelIdeal M hM hT
--       let J := modelIdeal E hE hTE
--       ∃ (δ : Ordinal.{0}) (P : Oracle) (φ : SentenceForm),
--         δ.toZFSet ∈ M ∧ φ.bound ≤ 2 ∧ P ∈ modelReals E ∧
--         let N := RealGeneratedModel.hull M (realCode P)
--         RealGeneratedModel.Contains M (realCode P) N ∧ (N : Set ZFSet.{0}).Countable ∧
--           ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
--             (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
--               fX.val H.carrier = definedSubset
--                 (level (groundReals (genericExtensionSet N c H.carrier)) δ)
--                   φ (fun _ : Fin φ.bound => realCode P) ∧
--               OwnDegreeExtension (genericExtensionSet N c H.carrier)
--                 (idealSet I) (automorphismSet ρ) (fX.val H.carrier)) ∧
--             ∃ GX : GenericFilter (Conditions c), GroundGeneric N GX ∧
--               genericExtensionSet N c GX.carrier = E ∧
--               ∃ σ : J ≃o J, RestrictsTo π J σ ∧ fX.val GX.carrier = automorphismSet σ
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.instSemilatticeSupDegree`, `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.OracleJump.jump`, `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal`, `OAI.TuringRigidity.RecursiveNames.Name`, `OAI.TuringRigidity.SetDegreeDecoding.automorphismSet`, `OAI.TuringRigidity.SetDegreeDecoding.idealSet`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.TransitiveNameModel.label`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder`, `OAI.TuringRigidity.RecursiveNames.Name.encode` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.InternallyCountable`, `OAI.TuringRigidity.ElementaryModel.SentenceForm`, `OAI.TuringRigidity.InternalCountableOrdinals.FirstUncountable`, `OAI.TuringRigidity.RelativeConstructible.groundReals`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.orderSet` and `OAI.TuringRigidity.ElementaryModel.SentenceForm.bound` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedForcing.OwnDegreeExtension`, `OAI.TuringRigidity.BoundedSetTheory.SourceT`, `OAI.TuringRigidity.BoundedSetTheory.realCode` and `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet_transitive` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenGroundPoset.conditions` and `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistentRestrictions.RestrictsTo` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.BoundedSetTheory.modelReals`, `OAI.TuringRigidity.CohenNiceNameConstruction.cohenTop`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.orderSet_pair` and `OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RealGeneratedModel.Contains`, `OAI.TuringRigidity.RealGeneratedModel.hull`, `OAI.TuringRigidity.RelativeConstructible.definedSubset` and `OAI.TuringRigidity.RelativeConstructible.level` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.BoundedSetTheory.extension_sourceT`, `OAI.TuringRigidity.CohenGroundPoset.manyColumn_internal` and `OAI.TuringRigidity.ElementaryModel.modelIdeal` (definitions bundle `OAIQ064A008` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.prescribed_unrestricted_ground_program` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/PrescribedRealHullExtension.lean (declaration OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

section

attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing BoundedForcing
open CohenGroundPoset InternalCountableOrdinals ElementaryModel SetDegreeDecoding PersistentRestrictions
open FullSetForcing OriginalRealDefinitionTransport
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem prescribed_real_hull_extension (π : Degree ≃o Degree)
    (M K : ZFSet.{0}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : GroundGeneric M G) :
    let c := conditions (ZFSet.prod K ZFSet.omega)
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT (manyColumn_internal M K hM hT hK.2.1).1
      (manyColumn_internal M K hM hT hK.2.1).2 (InternalCollapse.orderSet_pair c)
        G hG (G.upper le_top G.nonempty.choose_spec)
    let I := modelIdeal M hM hT
    let J := modelIdeal E hE hTE
    ∃ (δ : Ordinal.{0}) (P : Oracle) (φ : SentenceForm),
      δ.toZFSet ∈ M ∧ φ.bound ≤ 2 ∧ P ∈ modelReals E ∧
      let N := RealGeneratedModel.hull M (realCode P)
      RealGeneratedModel.Contains M (realCode P) N ∧ (N : Set ZFSet.{0}).Countable ∧
        ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
          (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
            fX.val H.carrier = definedSubset
              (level (groundReals (genericExtensionSet N c H.carrier)) δ)
                φ (fun _ : Fin φ.bound => realCode P) ∧
            OwnDegreeExtension (genericExtensionSet N c H.carrier)
              (idealSet I) (automorphismSet ρ) (fX.val H.carrier)) ∧
          ∃ GX : GenericFilter (Conditions c), GroundGeneric N GX ∧
            genericExtensionSet N c GX.carrier = E ∧
            ∃ σ : J ≃o J, RestrictsTo π J σ ∧ fX.val GX.carrier = automorphismSet σ := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
