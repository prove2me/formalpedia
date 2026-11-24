-- Prove2me | Theorems.Thm_GlobalTheory_SympTower_exists_pairs
-- name    : GlobalTheory.SympTower.exists_pairs
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:25:00.101504+00:00
-- url     : https://prove2.me/theorems/ecc4366d-26d8-41f7-9ee6-ab0056981a3f
-- title:
--   Symp Tower: exists pairs
-- statement:
--   The Symp Tower construction uses the exists pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompatibleSymplectic.lean#L66-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompatibleSymplectic.lean#L66-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompatibleSymplectic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SympTower

theorem GlobalTheory.SympTower.exists_pairs {n : ℕ} [NeZero n] {g : ℕ}
    (ω : (Fin (2 * g) → ZMod n) →ₗ[ZMod n] (Fin (2 * g) → ZMod n) →ₗ[ZMod n] ZMod n)
    (halt : ∀ x, ω x x = 0) (hnd : ∀ x, (∀ y, ω x y = 0) → x = 0) (k : ℕ) (hk : k ≤ g) :
    ∃ v w : Fin k → (Fin (2 * g) → ZMod n), (∀ i j, ω (v i) (v j) = 0) ∧
      (∀ i j, ω (w i) (w j) = 0) ∧ ∀ i j, ω (v i) (w j) = if i = j then 1 else 0 := by sorry
