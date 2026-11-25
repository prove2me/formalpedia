-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_finrank_eq
-- name    : GlobalTheory.FinEt.IsSplitOfRank.finrank_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:42.832224+00:00
-- url     : https://prove2.me/theorems/c6821e27-8b2b-5b23-9675-59c10f932d2c
-- title:
--   Is Split Of Rank: finrank eq
-- statement:
--   The Is Split Of Rank construction uses the finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L558-L571
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L558-L571

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

theorem GlobalTheory.FinEt.IsSplitOfRank.finrank_eq {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ} (h : IsSplitOfRank p n)
    (s : S) : p.finrank s = n := by sorry
