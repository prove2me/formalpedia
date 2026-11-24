-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_pullback_snd
-- name    : GlobalTheory.FinEt.IsSplitOfRank.pullback_snd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:24:10.054116+00:00
-- url     : https://prove2.me/theorems/c22031a2-ef89-442a-91ec-805f020479c9
-- title:
--   Is Split Of Rank: pullback snd
-- statement:
--   The Is Split Of Rank construction uses the pullback snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L432-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L432-L434

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}

theorem GlobalTheory.FinEt.IsSplitOfRank.pullback_snd {X S S' : Scheme.{u}} {p : X ⟶ S} {n : ℕ}
    (h : IsSplitOfRank p n) (t : S' ⟶ S) : IsSplitOfRank (pullback.snd p t) n := by sorry
