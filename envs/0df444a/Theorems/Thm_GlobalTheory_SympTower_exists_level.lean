-- Prove2me | Theorems.Thm_GlobalTheory_SympTower_exists_level
-- name    : GlobalTheory.SympTower.exists_level
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:24:59.291792+00:00
-- url     : https://prove2.me/theorems/7067f77e-6496-4ec4-a297-7ec6cf55db77
-- title:
--   Symp Tower: exists level
-- statement:
--   The Symp Tower construction uses the exists level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompatibleSymplectic.lean#L136-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompatibleSymplectic.lean#L136-L205

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

theorem GlobalTheory.SympTower.exists_level {F : Type} [Field F] {ζ : Fˣ} {n : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) {g : ℕ} {G : Type} [AddCommGroup G] (e : G → G → Fˣ)
    (Φ : G ≃+ (Fin (2 * g) → ZMod n)) (h1 : ∀ x y z, e (x + y) z = e x z * e y z)
    (h2 : ∀ x y z, e x (y + z) = e x y * e x z) (h3 : ∀ x, e x x = 1)
    (h4 : ∀ x, (∀ y, e x y = 1) → x = 0) :
    ∃ ev : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G,
      ∀ a b, e (ev a) (ev b) = ζ ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) := by sorry
