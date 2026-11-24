-- Prove2me | Theorems.Thm_GlobalTheory_RedFlatRow_piCongrLeft_freeEquiv
-- name    : GlobalTheory.RedFlatRow.piCongrLeft_freeEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:36:03.381221+00:00
-- url     : https://prove2.me/theorems/0cf70e5f-e0ba-462a-82fd-942382db10c8
-- title:
--   Red Flat Row: pi Congr Left free Equiv
-- statement:
--   The Red Flat Row construction uses the pi Congr Left free Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEqFlatMapFourierJacobiRow.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEqFlatMapFourierJacobiRow.lean#L48-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqFlatMapFourierJacobiRow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.RedFlatRow
open GlobalTheory.PartRed GlobalTheory.LocFlat
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.RedFlatRow.piCongrLeft_freeEquiv [MeasurableSpace k] (ρ : ℕ)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    MeasurableEquiv.piCongrLeft (fun _ => k) (freeEquiv n n' c ρ) y =
      fun rs => y ((freeEquiv n n' c ρ).symm rs) := by sorry
