-- Prove2me | Theorems.Thm_GlobalTheory_LocalGrouping_finsum_fibres_eq
-- name    : GlobalTheory.LocalGrouping.finsum_fibres_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:44.316342+00:00
-- url     : https://prove2.me/theorems/f4c617f0-ca64-4228-a0a7-42624c9b45ee
-- title:
--   Local Grouping: finsum fibres eq
-- statement:
--   The Local Grouping construction uses the finsum fibres eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumRestrictedProductCount.lean#L52-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumRestrictedProductCount.lean#L52-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumRestrictedProductCount
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
open GlobalTheory GlobalTheory.LocalGrouping
open Function

theorem GlobalTheory.LocalGrouping.finsum_fibres_eq (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ)
    (ℓ : R → ∀ i, D i) (A : Set R) (k m : ℕ)
    (T : Finset I) (u : ∀ i, D i) (hTS : (T : Set I) ⊆ S)
    (hfin : ∀ i ∈ S, (support (B i)).Finite)
    (hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0)
    (H3 : ∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1)
    (H4 : ∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) →
      Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) :
    (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k =
      (2 : ℂ) ^ m * ∑ᶠ f : (∀ i : T, D i), ∏ i : T, B i (f i) := by sorry
