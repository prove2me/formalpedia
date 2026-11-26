-- Prove2me | Theorems.Thm_MellinDuality_parseval_identity
-- name    : MellinDuality.parseval_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:10.760018+00:00
-- url     : https://prove2.me/theorems/93763651-d9c8-461e-8dee-dfb5b8f1f3df
-- title:
--   Mellin Duality: parseval identity
-- statement:
--   **Parseval** (Proposition 7.1): `∑_{ψ mod p} |∑_{n ≤ N} ψ(n) ε_n|² = (p - 1) N`, `N = (p-1)/2`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L199-L202
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L199-L202

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.parseval_identity :
    ∑ ψ : DirichletCharacter ℂ p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (eps p n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) := by sorry
