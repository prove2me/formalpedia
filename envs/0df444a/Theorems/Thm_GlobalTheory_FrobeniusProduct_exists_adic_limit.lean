-- Prove2me | Theorems.Thm_GlobalTheory_FrobeniusProduct_exists_adic_limit
-- name    : GlobalTheory.FrobeniusProduct.exists_adic_limit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:30.754347+00:00
-- url     : https://prove2.me/theorems/689dc608-8acf-413b-a231-1b2bda7d723f
-- title:
--   Frobenius Product: exists adic limit
-- statement:
--   The Frobenius Product construction uses the exists adic limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitFrobeniusIterateProductEq.lean#L5-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitFrobeniusIterateProductEq.lean#L5-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitFrobeniusIterateProductEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FrobeniusProduct

theorem GlobalTheory.FrobeniusProduct.exists_adic_limit {A : Type} [CommRing A] (I : Ideal A) [IsPrecomplete I A]
    (s : ℕ → A) (hs : ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r) :
    ∃ L : A, ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s m - L ∈ I ^ r := by sorry
