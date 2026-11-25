-- Prove2me | Theorems.Thm_GlobalTheory_T_finsum_restricted_product_count
-- name    : GlobalTheory.T.finsum_restricted_product_count
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:13.260851+00:00
-- url     : https://prove2.me/theorems/928d4b6b-2144-42fc-a389-e27479fce7ff
-- title:
--   T: finsum restricted product count
-- statement:
--   The T construction uses the finsum restricted product count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumRestrictedProductCountStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumRestrictedProductCountStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCount
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCountStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finsum_restricted_product_count : ∀ (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ) (ℓ : R → ∀ i, D i) (A : Set R) (k m : ℕ), (∀ i, Nonempty (D i)) → (∀ i ∈ S, (Function.support (B i)).Finite) → (∀ᶠ i in cofinite, ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0) → (∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1) → (∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) → Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) → (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k = (2 : ℂ) ^ m * ∏ᶠ i ∈ S, ∑ᶠ d, B i d := by sorry
