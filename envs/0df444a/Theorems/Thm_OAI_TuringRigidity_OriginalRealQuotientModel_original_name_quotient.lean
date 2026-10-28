-- Prove2me | Theorems.Thm_OAI_TuringRigidity_OriginalRealQuotientModel_original_name_quotient
-- name    : OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:42:08.396609+00:00
-- url     : https://prove2.me/theorems/7ba256f1-bc11-4436-a250-49056f5b0640
-- title:
--   OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient` of [lean/OAI/Computability/DegreeRigidity/Representation/OriginalRealQuotientModel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/OriginalRealQuotientModel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.OriginalRealQuotientModel`, with `open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames`, `open CohenGroundPoset InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax`, `open InternalProjectedGeneric`):
--
--   ```lean
--   theorem original_name_quotient (M K : ZFSet.{0})
--       (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M)
--       (τ : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
--       (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M) :
--       ∃ C ∈ M, ∃ _hCK : C ⊆ K, (C = ∅ ∨ InternallyCountable M C) ∧
--         ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
--           (∀ n, E n ∈ M ∧ E n ⊆ conditions (ZFSet.prod C ZFSet.omega)) ∧
--           ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
--             (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode (conditions (ZFSet.prod C ZFSet.omega)) U) ∧
--             (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
--             A = InternalGeneratedAlgebra.generated (conditions (ZFSet.prod C ZFSet.omega)) B Q
--               (InternalBooleanBits.seeds (conditions (ZFSet.prod C ZFSet.omega)) B E) ∧
--             Closed (conditions (ZFSet.prod C ZFSet.omega)) B Q A ∧
--             ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
--               ∃ hBA : ZFSet.prod C ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega,
--               ∀ G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
--                 AtomicForcing.GroundGeneric M G → τ.val G.carrier ⊆ ZFSet.omega →
--                 let J := InternalCohenProjectedGeneric.projected _ _ hBA G
--                 let X := τ.val G.carrier
--                 ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
--                   σ.val H.carrier = X ∧
--                   genericExtensionSet M (positive A) H.carrier = RealGeneratedModel.hull M X ∧
--                   RealGeneratedModel.Contains M X (RealGeneratedModel.hull M X) ∧
--                   let q := InternalQuotientConditions.conditions (conditions (ZFSet.prod C ZFSet.omega)) A
--                     (genericFilterSet (positive A) H.carrier)
--                   q ∈ RealGeneratedModel.hull M X ∧ InternalCollapse.orderSet q ∈ RealGeneratedModel.hull M X ∧
--                   ∃ Gq : GenericFilter (Conditions q), AtomicForcing.GroundGeneric (RealGeneratedModel.hull M X) Gq ∧
--                     genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier =
--                       genericExtensionSet M (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
--                     genericFilterSet q Gq.carrier =
--                       genericFilterSet (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
--                     genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier ⊆
--                       genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
--                     ∀ p ∈ G.carrier, ∃ r ∈ Gq.carrier,
--                       label q r = label _ (InternalCohenFactor.project _ _ hBA p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.RecursiveNames.Name`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.TransitiveNameModel.label`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder`, `OAI.TuringRigidity.RecursiveNames.Name.encode` and `OAI.TuringRigidity.RecursiveNames.Name.val` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.InternallyCountable`, `OAI.TuringRigidity.InternalBooleanBits.seeds`, `OAI.TuringRigidity.InternalBooleanSyntax.Closed`, `OAI.TuringRigidity.InternalGeneratedAlgebra.generated`, `OAI.TuringRigidity.InternalProjectedGeneric.positive`, `OAI.TuringRigidity.InternalQuotientConditions.conditions`, `OAI.TuringRigidity.InternalRegularAlgebra.IsCode` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.orderSet` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.BoundedSetTheory.orbitGraph`, `OAI.TuringRigidity.CohenGroundPoset.conditions`, `OAI.TuringRigidity.InternalProjectedGeneric.codePreorder` and `OAI.TuringRigidity.TransitiveNameModel.genericFilterSet` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.InternalCohenFactor.project` and `OAI.TuringRigidity.InternalCohenProjectedGeneric.projected` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RealGeneratedModel.Contains` and `OAI.TuringRigidity.RealGeneratedModel.hull` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.OriginalRealFullIteration.original_name_full_iteration` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/OriginalRealQuotientModel.lean (declaration OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A006
import Definitions.Def_OAIQ064A007

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OriginalRealQuotientModel
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
attribute [local instance] codeOrder codePreorder

theorem original_name_quotient (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M)
    (τ : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M) :
    ∃ C ∈ M, ∃ _hCK : C ⊆ K, (C = ∅ ∨ InternallyCountable M C) ∧
      ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
        (∀ n, E n ∈ M ∧ E n ⊆ conditions (ZFSet.prod C ZFSet.omega)) ∧
        ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
          (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode (conditions (ZFSet.prod C ZFSet.omega)) U) ∧
          (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
          A = InternalGeneratedAlgebra.generated (conditions (ZFSet.prod C ZFSet.omega)) B Q
            (InternalBooleanBits.seeds (conditions (ZFSet.prod C ZFSet.omega)) B E) ∧
          Closed (conditions (ZFSet.prod C ZFSet.omega)) B Q A ∧
          ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
            ∃ hBA : ZFSet.prod C ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega,
            ∀ G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))),
              AtomicForcing.GroundGeneric M G → τ.val G.carrier ⊆ ZFSet.omega →
              let J := InternalCohenProjectedGeneric.projected _ _ hBA G
              let X := τ.val G.carrier
              ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
                σ.val H.carrier = X ∧
                genericExtensionSet M (positive A) H.carrier = RealGeneratedModel.hull M X ∧
                RealGeneratedModel.Contains M X (RealGeneratedModel.hull M X) ∧
                let q := InternalQuotientConditions.conditions (conditions (ZFSet.prod C ZFSet.omega)) A
                  (genericFilterSet (positive A) H.carrier)
                q ∈ RealGeneratedModel.hull M X ∧ InternalCollapse.orderSet q ∈ RealGeneratedModel.hull M X ∧
                ∃ Gq : GenericFilter (Conditions q), AtomicForcing.GroundGeneric (RealGeneratedModel.hull M X) Gq ∧
                  genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier =
                    genericExtensionSet M (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
                  genericFilterSet q Gq.carrier =
                    genericFilterSet (conditions (ZFSet.prod C ZFSet.omega)) J.carrier ∧
                  genericExtensionSet (RealGeneratedModel.hull M X) q Gq.carrier ⊆
                    genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
                  ∀ p ∈ G.carrier, ∃ r ∈ Gq.carrier,
                    label q r = label _ (InternalCohenFactor.project _ _ hBA p) := by
  sorry

end TuringRigidity.OriginalRealQuotientModel

end OAI
end
