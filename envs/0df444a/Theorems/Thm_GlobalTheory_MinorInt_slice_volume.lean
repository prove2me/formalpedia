-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_slice_volume
-- name    : GlobalTheory.MinorInt.slice_volume
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:25:47.865264+00:00
-- url     : https://prove2.me/theorems/ffdbf02f-f2af-4354-9a1b-5e3f9d6bc7af
-- title:
--   Minor Int: slice volume
-- statement:
--   The Minor Int construction uses the slice volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L157-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L157-L228

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt

theorem GlobalTheory.MinorInt.slice_volume (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ENNReal, K < ⊤ ∧ ∀ (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ),
      (∀ i j, ‖(Aᴴ * A - Cᴴ * C - 1 : Matrix ι ι ℂ) i j‖ < δ) →
      volume {v : ι ⊕ κ → ℂ | (∀ i, ‖(Aᴴ *ᵥ (v ∘ Sum.inl) - Cᴴ *ᵥ (v ∘ Sum.inr)) i‖ ≤ 1) ∧
        ∑ c, ‖v (Sum.inr c)‖ ^ 2 - ∑ a, ‖v (Sum.inl a)‖ ^ 2 ≤ 2} ≤ K := by sorry
