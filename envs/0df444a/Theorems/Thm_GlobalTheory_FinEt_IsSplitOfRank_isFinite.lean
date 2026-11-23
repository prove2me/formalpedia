-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_isFinite
-- name    : GlobalTheory.FinEt.IsSplitOfRank.isFinite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:07.426874+00:00
-- url     : https://prove2.me/theorems/ca3fe0ec-e600-4562-a579-4dae1f54e57d
-- title:
--   Is Split Of Rank: is Finite
-- statement:
--   The Is Split Of Rank construction uses the is Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L543-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L543-L556

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

theorem GlobalTheory.FinEt.IsSplitOfRank.isFinite {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ} (h : IsSplitOfRank p n) :
    IsFinite p := by sorry
