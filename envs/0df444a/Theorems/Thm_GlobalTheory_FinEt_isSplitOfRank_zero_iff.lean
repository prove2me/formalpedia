-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_zero_iff
-- name    : GlobalTheory.FinEt.isSplitOfRank_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:08.379115+00:00
-- url     : https://prove2.me/theorems/d4e41c56-352b-4d59-b6e7-3fe76772b598
-- title:
--   Fin Et: is Split Of Rank zero iff
-- statement:
--   The Fin Et construction uses the is Split Of Rank zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L443-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L443-L450

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

theorem GlobalTheory.FinEt.isSplitOfRank_zero_iff {X S : Scheme.{u}} (p : X ⟶ S) :
    IsSplitOfRank p 0 ↔ IsEmpty X := by sorry
