-- Prove2me | Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_exists_groundInitialExternalBoundedGeometry
-- name    : OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialExternalBoundedGeometry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T05:56:49.714125+00:00
-- url     : https://prove2.me/theorems/f1c914d9-69f8-4236-8991-ee6e215160f2
-- title:
--   OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialExternalBoundedGeometry: intermediate lemma from OpenAI, The Partition Principle does not imply Choice
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialExternalBoundedGeometry` of [lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundBoundedExternalBirths.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundBoundedExternalBirths.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PartitionPilot.Forcing.TransitiveGround`, with `open SetFormula`):
--
--   ```lean
--   theorem exists_groundInitialExternalBoundedGeometry
--       (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
--       (unions : Realize M.sets SetFormula.union Fin.elim0)
--       (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
--       (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
--       (choice : Realize M.sets SetFormula.choice Fin.elim0)
--       {P G r μ A Labels m inv one τ C D rD c original base old T0 : ZFSet.{u}}
--       (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
--       (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
--       (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
--       (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
--       (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
--       (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
--       (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
--       (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
--       (originalCode : StrictLexHeightCode P C D r original rD)
--       (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
--       (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
--       (coordinateInjection : InjectionCode D ZFSet.omega c)
--       (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
--       (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
--       (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
--       (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
--       (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
--       (priorHeight : prior.height base = original) :
--       let I := M.groundEligibleTasks P G r μ A Labels
--       let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
--       let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
--       let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
--       let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
--       let T := M.groundTaskTransport P G r μ A Labels
--       I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
--         ∃ Reps ∈ M.sets,
--           ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
--             P r μ A τ I Sources Reps G m inv one T Filters,
--           ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
--             I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
--             GroundExternalGeometryInputs M (M.initialCompressionData P G r μ A Labels)
--               I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion ∧
--             GroundExternalGeometryData M (M.initialCompressionData P G r μ A Labels)
--               I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
--             GroundExternalBoundedGeometryData M (M.initialCompressionData P G r μ A Labels)
--               I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion
--   ```
--
--   **Definitions.** The statement is written with `OAI.PartitionPilot.Forcing.GroupCode`, `OAI.PartitionPilot.Forcing.MeetOrderCode`, `OAI.PartitionPilot.Forcing.PosetActionCode`, `OAI.PartitionPilot.Forcing.StrictLexHeightCode`, `OAI.PartitionPilot.Forcing.relationImage` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundRelations` (definitions bundle `OAIQ253P000` of this split); `OAI.PartitionPilot.Forcing.DenseOrderCode`, `OAI.PartitionPilot.Forcing.literalTaskFilterGraph`, `OAI.PartitionPilot.Forcing.literalTaskSeparatorGraph`, `OAI.PartitionPilot.Forcing.literalTaskSourceGraph` and `OAI.PartitionPilot.Forcing.literalTaskTargetGraph` (definitions bundle `OAIQ253P001` of this split); `OAI.PartitionPilot.Forcing.GroundBornCompression`, `OAI.PartitionPilot.Forcing.GroundHeightedCompression` and `OAI.PartitionPilot.Forcing.GroundProfiledCompression` (definitions bundle `OAIQ253P002` of this split); `OAI.PartitionPilot.Forcing.GroundChronologicalHistory` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundMeetFilters` (definitions bundle `OAIQ253P003` of this split); `OAI.PartitionPilot.Forcing.GroundChronologicalCompression`, `OAI.PartitionPilot.Forcing.GroundCompressionOrigin`, `OAI.PartitionPilot.Forcing.GroundExternalBoundedGeometryData`, `OAI.PartitionPilot.Forcing.GroundExternalGeometryData` and `OAI.PartitionPilot.Forcing.GroundExternalGeometryInputs` (definitions bundle `OAIQ253P004` of this split); `OAI.PartitionPilot.Forcing.TransitiveGround.groundEligibleTasks`, `OAI.PartitionPilot.Forcing.TransitiveGround.groundTaskTransport` and `OAI.PartitionPilot.Forcing.TransitiveGround.initialCompressionData` (definitions bundle `OAIQ253P005` of this split); `OAI.PartitionPilot.Forcing.InjectionCode`, `OAI.PartitionPilot.Forcing.TransitiveGround`, `OAI.PartitionPilot.Forcing.ordinalSetProperty`, `OAI.PartitionPilot.Forcing.SetFormula.CollectionSchema`, `OAI.PartitionPilot.Forcing.SetFormula.Realize`, `OAI.PartitionPilot.Forcing.SetFormula.SeparationSchema`, `OAI.PartitionPilot.Forcing.SetFormula.choice`, `OAI.PartitionPilot.Forcing.SetFormula.infinity`, `OAI.PartitionPilot.Forcing.SetFormula.pairing`, `OAI.PartitionPilot.Forcing.SetFormula.powerSet`, `OAI.PartitionPilot.Forcing.SetFormula.union` and `OAI.PartitionPilot.Forcing.TransitiveGround.groundEmbeddable` (the published bundle `Def_PartitionPrinciple`).
--
--   **Used by.** The proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialMainSuccessor` of this split imports it.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/SetTheory/PartitionPrinciple/Definability/GroundBoundedExternalBirths.lean (declaration OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialExternalBoundedGeometry)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P004
import Definitions.Def_OAIQ253P005

section

attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialExternalBoundedGeometry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalGeometryInputs M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalBoundedGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion := by
  sorry

end TransitiveGround

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end
