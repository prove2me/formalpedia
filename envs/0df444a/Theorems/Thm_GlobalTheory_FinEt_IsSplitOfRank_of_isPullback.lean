-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_of_isPullback
-- name    : GlobalTheory.FinEt.IsSplitOfRank.of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:54.280527+00:00
-- url     : https://prove2.me/theorems/f0d026fd-0791-4966-9014-03b22af45429
-- title:
--   Is Split Of Rank: of is Pullback
-- statement:
--   The Is Split Of Rank construction uses the of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L421-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L421-L430

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

theorem GlobalTheory.FinEt.IsSplitOfRank.of_isPullback {X S X' S' : Scheme.{u}} {a : X' ⟶ X} {q : X' ⟶ S'}
    {p : X ⟶ S} {t : S' ⟶ S} (H : IsPullback a q p t) {n : ℕ} (h : IsSplitOfRank p n) :
    IsSplitOfRank q n := by sorry
