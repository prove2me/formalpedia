-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_exists_isSplitOfRank_pullback
-- name    : GlobalTheory.FinEt.exists_isSplitOfRank_pullback
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:08.984271+00:00
-- url     : https://prove2.me/theorems/c2434c23-9bec-4a04-9037-bddd172c854d
-- title:
--   Fin Et: exists is Split Of Rank pullback
-- statement:
--   The Fin Et construction uses the exists is Split Of Rank pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L605-L610
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L605-L610

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

theorem GlobalTheory.FinEt.exists_isSplitOfRank_pullback {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p] [Etale p]
    {n : ℕ} (hn : ∀ s, p.finrank s = n) :
    ∃ (S' : Scheme.{u}) (t : S' ⟶ S), IsFinite t ∧ Etale t ∧ Surjective t ∧
      IsSplitOfRank (pullback.snd p t) n := by sorry
