-- Prove2me | Theorems.Thm_GlobalTheory_OrderProductDifference_order_prod_sub_prod
-- name    : GlobalTheory.OrderProductDifference.order_prod_sub_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:18.782057+00:00
-- url     : https://prove2.me/theorems/a72733a3-8811-48c0-beb2-1b7f9a57a1e9
-- title:
--   Order Product Difference: order prod sub prod
-- statement:
--   The Order Product Difference construction uses the order prod sub prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrderProdSubProd.lean#L7-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrderProdSubProd.lean#L7-L40

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

theorem GlobalTheory.OrderProductDifference.order_prod_sub_prod {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (a i))
    (hb : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) ≤ MvPowerSeries.order (b i))
    (hab : ∀ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) :
    ∑ i ∈ s, ((k i : ℕ) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by sorry
