-- Prove2me | Theorems.Thm_GlobalTheory_MulSubOneValuation_mul_sub_one_le_of_valuation
-- name    : GlobalTheory.MulSubOneValuation.mul_sub_one_le_of_valuation
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:12.179246+00:00
-- url     : https://prove2.me/theorems/344efd84-3e36-4be1-ab91-570c66eee248
-- title:
--   Mul Sub One Valuation: mul sub one le of valuation
-- statement:
--   The Mul Sub One Valuation construction uses the mul sub one le of valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MulSubOneLeOfValuation.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MulSubOneLeOfValuation.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MulSubOneLeOfValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MulSubOneValuation

theorem GlobalTheory.MulSubOneValuation.mul_sub_one_le_of_valuation {K Γ : Type*} [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} {γ : Γ} (hγ : γ ≤ 1) {A B : Matrix (Fin n) (Fin n) K}
    (hA : ∀ r s, v (A r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ)
    (hB : ∀ r s, v (B r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ) (r s : Fin n) :
    v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ := by sorry
