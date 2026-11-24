-- Prove2me | Theorems.Thm_GlobalTheory_SympTower_ker_and_surj
-- name    : GlobalTheory.SympTower.ker_and_surj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:25:14.752642+00:00
-- url     : https://prove2.me/theorems/a64156c3-488b-482f-accf-a15d82bebf1c
-- title:
--   Symp Tower: ker and surj
-- statement:
--   The Symp Tower construction uses the ker and surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompatibleSymplectic.lean#L207-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompatibleSymplectic.lean#L207-L263

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

theorem GlobalTheory.SympTower.ker_and_surj {F : Type} [Field F] {ζ : Fˣ} {n : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) {g : ℕ} {G : Type} [AddCommGroup G] (e : G → G → Fˣ)
    (Φ : G ≃+ (Fin (2 * g) → ZMod n)) (h1 : ∀ x y z, e (x + y) z = e x z * e y z)
    (ev : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G)
    (hev : ∀ a b, e (ev a) (ev b) = ζ ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1)) :
    (∀ a b, ev a = ev b ↔ ∃ e', a = b + n • e') ∧ Function.Surjective ev := by sorry
