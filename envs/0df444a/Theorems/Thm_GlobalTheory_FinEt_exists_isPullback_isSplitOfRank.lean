-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_exists_isPullback_isSplitOfRank
-- name    : GlobalTheory.FinEt.exists_isPullback_isSplitOfRank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:17.742792+00:00
-- url     : https://prove2.me/theorems/a7dca9ae-cbbe-4ecb-91a7-3556c5aea38d
-- title:
--   Fin Et: exists is Pullback is Split Of Rank
-- statement:
--   The Fin Et construction uses the exists is Pullback is Split Of Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L573-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L573-L603

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

theorem GlobalTheory.FinEt.exists_isPullback_isSplitOfRank (n : ℕ) {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p]
    [Etale p] (hn : ∀ s, p.finrank s = n) :
    ∃ (S' X' : Scheme.{u}) (t : S' ⟶ S) (a : X' ⟶ X) (q : X' ⟶ S'),
      IsFinite t ∧ Etale t ∧ Surjective t ∧ IsPullback a q p t ∧ IsSplitOfRank q n := by sorry
