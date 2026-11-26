-- Prove2me | Theorems.Thm_MellinDuality_parseval_any_weight
-- name    : MellinDuality.parseval_any_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:58.923801+00:00
-- url     : https://prove2.me/theorems/e9c8344b-d516-48fd-8d31-f834750cb759
-- title:
--   Mellin Duality: parseval any weight
-- statement:
--   Parseval for any weight `w` with `w(n)² = 1`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L205-L209
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L205-L209

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.parseval_any_weight (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ : DirichletCharacter ℂ p,
        ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) := by sorry
