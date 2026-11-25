-- Prove2me | Theorems.Thm_GlobalTheory_OrderProductDifference_target
-- name    : GlobalTheory.OrderProductDifference.target
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:54.310271+00:00
-- url     : https://prove2.me/theorems/85404b2f-3b63-4558-afb5-d3bb266a5531
-- title:
--   Order Product Difference: target
-- statement:
--   The Order Product Difference construction uses the target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrderProdSubProd.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrderProdSubProd.lean#L42-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrderProdSubProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrderProductDifference
open MvPowerSeries

theorem GlobalTheory.OrderProductDifference.target : ∀ {R τ ι : Type} [inst : CommRing R] (s : Finset ι) (a b : ι → MvPowerSeries τ R) (k : ι → ℕ), (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (a i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (b i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) → ∑ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by sorry
