-- Prove2me | Theorems.Thm_MellinDuality_parseval_general
-- name    : MellinDuality.parseval_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:17.086799+00:00
-- url     : https://prove2.me/theorems/d50cc3fb-2700-4e6e-834c-ac54b4680e36
-- title:
--   Mellin Duality: parseval general
-- statement:
--   **Parseval** for any weight `w` with `w(n)² = 1`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Parseval.lean#L40-L78
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Parseval.lean#L40-L78

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Parseval
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.parseval_general (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ : DirichletCharacter ℂ p,
        ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) := by sorry
