-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralTrace_commonPowerAntichains
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonPowerAntichains
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:12:23.807642+00:00
-- url     : https://prove2.me/theorems/dbc6aa63-08c0-4ff8-971a-544a39ac6b32
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonPowerAntichains: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonPowerAntichains` of [lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticStructuralFinalRefinements.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticStructuralFinalRefinements.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetRealization SetFormula Compression.RecursiveMaps`):
--
--   ```lean
--   theorem semanticStructuralTrace_commonPowerAntichains :
--       letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
--       ∀ count (degrees : Fin count → Nat)
--         (tau : Fin count → (M.nameDomain (SetMembers.presentation Q)).names),
--         ∃ beta, ∃ _ : beta ∈ K, ∃ f : Fin count → ZFSet.{u}, ∀ i,
--           let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
--           f i ∈ M.sets ∧ ZFSet.IsFunc J (M.groundPower Q) (f i) ∧
--           (∀ sigma A, ZFSet.pair sigma A ∈ f i →
--             RelativeMaximalAntichainCode Q
--               (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
--               (M.ordinaryMembershipDecisions Q
--                 (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
--                 sigma (tau i).val.val) A ∧
--             ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
--               ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed ∧
--               ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed) ∧
--           (∀ sigma A, ZFSet.pair sigma A ∈ f i →
--             let lower := M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)
--             let lowerOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T beta
--               (graphRestriction beta packed)
--             A ⊆ lower ∧ ∀ q ∈ lower, ∃ p ∈ A, ∃ r ∈ lower,
--               ZFSet.pair r q ∈ lowerOrder ∧ ZFSet.pair r p ∈ lowerOrder)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.PosetAction`, `OAI.PartitionPilot.SetRealization.Presentation`, `OAI.PartitionPilot.SetRealization.SetMembers`, `OAI.PartitionPilot.Forcing.PosetAction.actionGraph` and `OAI.PartitionPilot.SetRealization.SetMembers.presentation` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.RelativeMaximalAntichainCode`, `OAI.PartitionPilot.Forcing.graphRestriction` and `OAI.PartitionPilot.Forcing.iteratedPairNameFamily` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.supportBasisCode`, `OAI.PartitionPilot.Forcing.PosetAction.principalFix` and `OAI.PartitionPilot.SetRealization.Presentation.conditionOrder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.Name`, `OAI.PartitionPilot.Forcing.OrdinalRecursionTrace`, `OAI.PartitionPilot.Forcing.PosetAction.act`, `OAI.PartitionPilot.Forcing.PosetAction.conditionMapFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.nameDomain`, `OAI.PartitionPilot.SetRealization.Presentation.pairEmpty` and `OAI.PartitionPilot.Forcing.Name.NameDomain` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily` and `OAI.PartitionPilot.Forcing.TransitiveGround.ordinaryMembershipDecisions` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryForcing` and `OAI.PartitionPilot.Forcing.TransitiveGround.refinementHistoryOrder` (definitions bundle `OAIQ253P007` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.structuralForcingStage` and `OAI.PartitionPilot.Forcing.TransitiveGround.structuralRefinementHistory` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.GroundBelow`, `OAI.PartitionPilot.Forcing.GroundStandardInaccessible`, `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet`, `OAI.PartitionPilot.Forcing.SetFormula.union` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundPower` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonRefinementNames` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundSemanticStructuralFinalRefinements.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonPowerAntichains)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
include hK hh standard trace infinite choice smallRows smallT

theorem semanticStructuralTrace_commonPowerAntichains :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    ∀ count (degrees : Fin count → Nat)
      (tau : Fin count → (M.nameDomain (SetMembers.presentation Q)).names),
      ∃ beta, ∃ _ : beta ∈ K, ∃ f : Fin count → ZFSet.{u}, ∀ i,
        let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
        f i ∈ M.sets ∧ ZFSet.IsFunc J (M.groundPower Q) (f i) ∧
        (∀ sigma A, ZFSet.pair sigma A ∈ f i →
          RelativeMaximalAntichainCode Q
            (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
            (M.ordinaryMembershipDecisions Q
              (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
              sigma (tau i).val.val) A ∧
          ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
            ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed ∧
            ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed) ∧
        (∀ sigma A, ZFSet.pair sigma A ∈ f i →
          let lower := M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)
          let lowerOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T beta
            (graphRestriction beta packed)
          A ⊆ lower ∧ ∀ q ∈ lower, ∃ p ∈ A, ∃ r ∈ lower,
            ZFSet.pair r q ∈ lowerOrder ∧ ZFSet.pair r p ∈ lowerOrder) := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end
