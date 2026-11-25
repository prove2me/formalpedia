-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_sigmaDesc
-- name    : GlobalTheory.FinEt.isSplitOfRank_sigmaDesc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:00.293916+00:00
-- url     : https://prove2.me/theorems/b21af0ec-eed8-4574-a3f2-33a5b3e700a9
-- title:
--   Fin Et: is Split Of Rank sigma Desc
-- statement:
--   The Fin Et construction uses the is Split Of Rank sigma Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L367-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L367-L369

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

theorem GlobalTheory.FinEt.isSplitOfRank_sigmaDesc (S : Scheme.{u}) (n : ℕ) :
    IsSplitOfRank (Sigma.desc fun _ : Fin n ↦ 𝟙 S) n := by sorry
