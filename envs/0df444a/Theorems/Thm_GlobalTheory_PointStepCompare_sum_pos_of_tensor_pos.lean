-- Prove2me | Theorems.Thm_GlobalTheory_PointStepCompare_sum_pos_of_tensor_pos
-- name    : GlobalTheory.PointStepCompare.sum_pos_of_tensor_pos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:32.250803+00:00
-- url     : https://prove2.me/theorems/37e2558b-48ef-4b86-bc14-611702588dff
-- title:
--   Point Step Compare: sum pos of tensor pos
-- statement:
--   The Point Step Compare construction uses the sum pos of tensor pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumPosOfTensorPos.lean#L134-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumPosOfTensorPos.lean#L134-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumPosOfTensorPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PointStepCompare
open NumberField Matrix
open scoped MatrixOrder

theorem GlobalTheory.PointStepCompare.sum_pos_of_tensor_pos : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (ι : Type) [Fintype ι] (a c : ι → Y), (∀ f g : Y →ₗ[ℤ] ℤ, ∑ i, f (a i) * g (c i) = ∑ i, g (a i) * f (c i)) → (∀ f : Y →ₗ[ℤ] ℤ, f ≠ 0 → 0 < ∑ i, f (a i) * f (c i)) → ∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ x y, γ x y = γ y x) → (∀ x, 0 ≤ γ x x) → γ ≠ 0 → 0 < ∑ i, γ (a i) (c i) := by sorry
