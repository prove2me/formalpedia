-- Prove2me | Theorems.Thm_MellinDuality_parseval
-- name    : MellinDuality.parseval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:03.698065+00:00
-- url     : https://prove2.me/theorems/ee90de2a-3da4-4510-8904-ca4e06634aa2
-- title:
--   Mellin Duality: parseval
-- statement:
--   **Parseval** (Proposition 7.1 of Paper II): with `N = (p - 1)/2` and
--   `ε_n = (-1)^{⌊n²/p⌋}`, `∑_{ψ mod p} |∑_{n ≤ N} ψ(n) ε_n|² = (p - 1) N`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Parseval.lean#L82-L86
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Parseval.lean#L82-L86

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Parseval
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.parseval :
    ∑ ψ : DirichletCharacter ℂ p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (eps p n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) := by sorry
