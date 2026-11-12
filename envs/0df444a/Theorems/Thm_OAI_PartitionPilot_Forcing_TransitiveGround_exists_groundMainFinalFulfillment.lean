-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_exists_groundMainFinalFulfillment
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:26:12.918851+00:00
-- url     : https://prove2.me/theorems/0a0f98ac-322d-4cc6-8e18-ad2136981d62
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment` of [lean/OAI/SetTheory/PartitionPrinciple/Geometry/GroundMainFinalFulfillmentConstruction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Geometry/GroundMainFinalFulfillmentConstruction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetFormula SetRealization`):
--
--   ```lean
--   theorem exists_groundMainFinalFulfillment
--       (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
--       (unions : Realize M.sets SetFormula.union Fin.elim0)
--       (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
--       (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
--       let C := M.groundOmegaOne pairing unions powers separation collection infinite
--       ∃ data : GroundMainOrdinalConstructionData M K C pairing unions powers separation,
--         ∃ ordinalC : ordinalSetProperty C,
--           letI := ordinalMainIndexPreorder ordinalC
--           ∃ run : GroundMainPrefix M K C C (rationalCarrier data.seed.fractionCode)
--               (rationalLtGraph data.seed.fractionCode) pairing unions powers separation (SetMembers C),
--             run.indices = C ∧ run.PreservesOldProfiles ∧
--             MainPrefixHistoryUnionCode data.history run.code ∧
--             MainPrefixHistoryExtends data.history run.code ∧
--             (∀ q, MainPrefixHistoryUnionCode data.history q → q = run.code) ∧
--             GroundBelow M run.indices K ∧ ZFSet.rank run.code < ZFSet.rank K ∧
--             ∃ i₀ : SetMembers C, run.key i₀ = ∅ ∧
--               ∃ fulfilled : run.FinalFulfillment data.level i₀,
--                 let geometry := run.finalGeometry i₀
--                 let inclusions := run.finalInclusions i₀
--                 geometry.code ∈ M.sets ∧ ZFSet.rank geometry.code < ZFSet.rank K ∧
--                 GroundBelow M geometry.carrier K ∧ GroundBelow M geometry.actors K ∧
--                 inclusions.pointFamily ∈ M.sets ∧ inclusions.actorFamily ∈ M.sets ∧
--                 ZFSet.rank inclusions.pointFamily < ZFSet.rank K ∧
--                 ZFSet.rank inclusions.actorFamily < ZFSet.rank K ∧
--                 fulfilled.chronology.serial.code ∈ M.sets ∧
--                 ∀ N : TransitiveGround.{u}, M.sets ⊆ N.sets →
--                   Realize N.sets SetFormula.pairing Fin.elim0 →
--                   Realize N.sets SetFormula.union Fin.elim0 →
--                   Realize N.sets powerSet Fin.elim0 → SeparationSchema N.sets →
--                   Realize N.sets infinity Fin.elim0 → Realize N.sets SetFormula.choice Fin.elim0 →
--                   ∀ F ∈ N.sets, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F →
--                     ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
--                       ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ geometry.order
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.MeetFilterCode` and `OAI.PartitionPilot.SetRealization.SetMembers` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.ordinalMainIndexPreorder` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry`, `OAI.PartitionPilot.Forcing.MainPrefixHistoryExtends`, `OAI.PartitionPilot.Forcing.MainPrefixHistoryUnionCode`, `OAI.PartitionPilot.Forcing.rationalCarrier`, `OAI.PartitionPilot.Forcing.rationalLtGraph` and `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.code` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.GroundSerializedChronology.code` (definitions bundle `OAIQ253P004` of this split); `OAI.PartitionPilot.Forcing.GroundMainFinalInclusions`, `OAI.PartitionPilot.Forcing.GroundMainOrdinalConstructionData`, `OAI.PartitionPilot.Forcing.GroundMainPrefix`, `OAI.PartitionPilot.Forcing.GroundInitialMainSeedData`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.PreservesOldProfiles`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.code`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.cutoffLimit`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.indices` and `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology` (definitions bundle `OAIQ253P006` of this split); `OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.finalGeometry`, `OAI.PartitionPilot.Forcing.GroundMainPrefix.finalInclusions` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundOmegaOne` (definitions bundle `OAIQ253P009` of this split); `OAI.PartitionPilot.Forcing.GroundBelow`, `OAI.PartitionPilot.Forcing.GroundStandardInaccessible`, `OAI.PartitionPilot.Forcing.InjectionCode`, `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet` and `OAI.PartitionPilot.Forcing.SetFormula.union` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Geometry/GroundMainFinalFulfillmentConstruction.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment)

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

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMainFinalFulfillment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ data : GroundMainOrdinalConstructionData M K C pairing unions powers separation,
      ∃ ordinalC : ordinalSetProperty C,
        letI := ordinalMainIndexPreorder ordinalC
        ∃ run : GroundMainPrefix M K C C (rationalCarrier data.seed.fractionCode)
            (rationalLtGraph data.seed.fractionCode) pairing unions powers separation (SetMembers C),
          run.indices = C ∧ run.PreservesOldProfiles ∧
          MainPrefixHistoryUnionCode data.history run.code ∧
          MainPrefixHistoryExtends data.history run.code ∧
          (∀ q, MainPrefixHistoryUnionCode data.history q → q = run.code) ∧
          GroundBelow M run.indices K ∧ ZFSet.rank run.code < ZFSet.rank K ∧
          ∃ i₀ : SetMembers C, run.key i₀ = ∅ ∧
            ∃ fulfilled : run.FinalFulfillment data.level i₀,
              let geometry := run.finalGeometry i₀
              let inclusions := run.finalInclusions i₀
              geometry.code ∈ M.sets ∧ ZFSet.rank geometry.code < ZFSet.rank K ∧
              GroundBelow M geometry.carrier K ∧ GroundBelow M geometry.actors K ∧
              inclusions.pointFamily ∈ M.sets ∧ inclusions.actorFamily ∈ M.sets ∧
              ZFSet.rank inclusions.pointFamily < ZFSet.rank K ∧
              ZFSet.rank inclusions.actorFamily < ZFSet.rank K ∧
              fulfilled.chronology.serial.code ∈ M.sets ∧
              ∀ N : TransitiveGround.{u}, M.sets ⊆ N.sets →
                Realize N.sets SetFormula.pairing Fin.elim0 →
                Realize N.sets SetFormula.union Fin.elim0 →
                Realize N.sets powerSet Fin.elim0 → SeparationSchema N.sets →
                Realize N.sets infinity Fin.elim0 → Realize N.sets SetFormula.choice Fin.elim0 →
                ∀ F ∈ N.sets, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F →
                  ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
                    ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ geometry.order := by
  sorry

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end
