-- Prove2me | Theorems.Thm_MellinDuality_parseval_odd_characters
-- name    : MellinDuality.parseval_odd_characters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:19.055663+00:00
-- url     : https://prove2.me/theorems/630a4186-8914-53d9-8b9f-6aa6eabfc7a1
-- title:
--   Mellin Duality: parseval odd characters
-- statement:
--   Parseval over the odd characters, for any weight with `w(n)² = 1`:
--   `∑_{χ odd} |∑_{n ≤ N} χ(n) w(n)|² = ((p - 1)/2) N`, `N = (p - 1)/2`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L221-L224
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L221-L224

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.parseval_odd_characters (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ ∈ oddChars p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) / 2 * ((p - 1) / 2 : ℕ) := by sorry
