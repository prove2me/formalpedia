-- Prove2me | Theorems.Thm_MellinDuality_parseval_odd
-- name    : MellinDuality.parseval_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:12.41322+00:00
-- url     : https://prove2.me/theorems/19de1c11-c53c-4e13-b828-714e2ff36f5b
-- title:
--   Mellin Duality: parseval odd
-- statement:
--   **Parseval over the odd characters**: for any weight `w` with `w(n)² = 1`,
--   `∑_{χ odd} |∑_{n ≤ N} χ(n) w(n)|² = ((p - 1)/2) N`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L67-L82
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L67-L82

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.parseval_odd (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ ∈ oddChars p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) / 2 * ((p - 1) / 2 : ℕ) := by sorry
