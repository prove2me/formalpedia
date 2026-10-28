-- Prove2me | Theorems.Thm_OAI_TuringRigidity_BoundedForcing_projected_arithmetic_output_cone
-- name    : OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:38:29.995993+00:00
-- url     : https://prove2.me/theorems/eb3f6628-bf6e-4296-b964-8d3ea86462b6
-- title:
--   OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone` of [lean/OAI/Computability/DegreeRigidity/SetModels/ProjectedArithmeticOutputCone.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/ProjectedArithmeticOutputCone.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.BoundedForcing`, with `open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing`, `open RelativeConstructible CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric`, `open InternalCohenFactor OracleJump TableIndices IndexMatrix`, `open PersistentRestrictions SetDegreeDecoding ElementaryModel FullSetForcing`):
--
--   ```lean
--   theorem projected_arithmetic_output_cone (M C B : ZFSet.{0}) [Countable (Conditions M)]
--       (hM : Transitive M) (hT : SourceT M) (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
--       (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : ElementaryModel.SentenceForm)
--       (I : CountableIdeal) (ρ : I ≃o I)
--       (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
--       (R : Oracle) (hRM : realCode R ∈ M)
--       (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val)
--       (f : Name (Conditions (conditions C))) (hf : f.encode (label (conditions C)) ∈ M)
--       (hfv : ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
--         f.val H.carrier = definedSubset
--           (level (groundReals (genericExtensionSet M (conditions C) H.carrier)) δ)
--             φ (fun _ : Fin φ.bound => Z))
--       (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
--       (hOwn : OwnDegreeExtension (genericExtensionSet M (conditions C) G.carrier)
--         (idealSet I) (automorphismSet ρ) (f.val G.carrier))
--       (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M)
--       (A : Oracle) (hτv : τ.val (projected C B hBC G).carrier = realCode A)
--       (p₀ : Conditions (conditions C)) (hp₀ : p₀ ∈ G.carrier) :
--       ∃ x y : Name (Conditions (conditions C)),
--         x.encode (label (conditions C)) ∈ M ∧ y.encode (label (conditions C)) ∈ M ∧
--         x.val G.carrier = realCode A ∧
--         (∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
--           τ.val (projected C B hBC H).carrier ⊆ ZFSet.omega →
--             x.val H.carrier = τ.val (projected C B hBC H).carrier) ∧
--         ∃ d : ℕ, ∃ p ∈ G.carrier, p ≤ p₀ ∧
--           ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
--             project C B hBC p ∈ (projected C B hBC H).carrier →
--               ∃ A' X' : Oracle, x.val H.carrier = realCode A' ∧ y.val H.carrier = realCode X' ∧
--                 Represents (iterate (join A' R) 5) (machine d) X' ∧
--                 ∃ a ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
--                 ∃ b ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
--                   realCode A' ∈ a ∧ realCode X' ∈ b ∧ ZFSet.pair a b ∈ f.val H.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.join`, `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.IndexMatrix.machine`, `OAI.TuringRigidity.OracleJump.iterate`, `OAI.TuringRigidity.OracleJump.jump`, `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal`, `OAI.TuringRigidity.RecursiveNames.Name`, `OAI.TuringRigidity.SetDegreeDecoding.automorphismSet`, `OAI.TuringRigidity.SetDegreeDecoding.idealSet`, `OAI.TuringRigidity.TableIndices.Represents`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.TransitiveNameModel.label`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder`, `OAI.TuringRigidity.RecursiveNames.Name.encode` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.ElementaryModel.SentenceForm`, `OAI.TuringRigidity.RelativeConstructible.groundReals` and `OAI.TuringRigidity.ElementaryModel.SentenceForm.bound` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedForcing.OwnDegreeExtension`, `OAI.TuringRigidity.BoundedSetTheory.SourceT`, `OAI.TuringRigidity.BoundedSetTheory.degreeUniverse` and `OAI.TuringRigidity.BoundedSetTheory.realCode` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenGroundPoset.conditions` and `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.InternalCohenFactor.project` and `OAI.TuringRigidity.InternalCohenProjectedGeneric.projected` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RelativeConstructible.definedSubset` and `OAI.TuringRigidity.RelativeConstructible.level` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.prescribed_unrestricted_ground_program` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/ProjectedArithmeticOutputCone.lean (declaration OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A006
import Definitions.Def_OAIQ064A007

section

attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open InternalCohenFactor OracleJump TableIndices IndexMatrix
open PersistentRestrictions SetDegreeDecoding ElementaryModel FullSetForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem projected_arithmetic_output_cone (M C B : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : ElementaryModel.SentenceForm)
    (I : CountableIdeal) (ρ : I ≃o I)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (R : Oracle) (hRM : realCode R ∈ M)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val)
    (f : Name (Conditions (conditions C))) (hf : f.encode (label (conditions C)) ∈ M)
    (hfv : ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (conditions C) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (hOwn : OwnDegreeExtension (genericExtensionSet M (conditions C) G.carrier)
      (idealSet I) (automorphismSet ρ) (f.val G.carrier))
    (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M)
    (A : Oracle) (hτv : τ.val (projected C B hBC G).carrier = realCode A)
    (p₀ : Conditions (conditions C)) (hp₀ : p₀ ∈ G.carrier) :
    ∃ x y : Name (Conditions (conditions C)),
      x.encode (label (conditions C)) ∈ M ∧ y.encode (label (conditions C)) ∈ M ∧
      x.val G.carrier = realCode A ∧
      (∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        τ.val (projected C B hBC H).carrier ⊆ ZFSet.omega →
          x.val H.carrier = τ.val (projected C B hBC H).carrier) ∧
      ∃ d : ℕ, ∃ p ∈ G.carrier, p ≤ p₀ ∧
        ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
          project C B hBC p ∈ (projected C B hBC H).carrier →
            ∃ A' X' : Oracle, x.val H.carrier = realCode A' ∧ y.val H.carrier = realCode X' ∧
              Represents (iterate (join A' R) 5) (machine d) X' ∧
              ∃ a ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
              ∃ b ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
                realCode A' ∈ a ∧ realCode X' ∈ b ∧ ZFSet.pair a b ∈ f.val H.carrier := by
  sorry

end TuringRigidity.BoundedForcing

end OAI
end
