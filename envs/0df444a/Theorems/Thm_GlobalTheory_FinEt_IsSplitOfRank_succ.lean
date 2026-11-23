-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_succ
-- name    : GlobalTheory.FinEt.IsSplitOfRank.succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:48.499176+00:00
-- url     : https://prove2.me/theorems/a7fa336c-cfa8-4c63-ab57-ef594c6ef072
-- title:
--   Is Split Of Rank: succ
-- statement:
--   The Is Split Of Rank construction uses the succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L452-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L452-L480

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

theorem GlobalTheory.FinEt.IsSplitOfRank.succ {X V S : Scheme.{u}} {p : X ⟶ S} (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    [IsOpenImmersion σ] (j : V ⟶ X) [IsOpenImmersion j] (hj : Set.range j = (Set.range σ)ᶜ)
    {n : ℕ} (h : IsSplitOfRank (j ≫ p) n) : IsSplitOfRank p (n + 1) := by sorry
