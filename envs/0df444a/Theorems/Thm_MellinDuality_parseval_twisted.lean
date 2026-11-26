-- Prove2me | Theorems.Thm_MellinDuality_parseval_twisted
-- name    : MellinDuality.parseval_twisted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:15.094908+00:00
-- url     : https://prove2.me/theorems/3a301c65-728b-5514-841d-9a2ce75f0054
-- title:
--   Mellin Duality: parseval twisted
-- statement:
--   The twisted Parseval sum vanishes: `∑_ψ ψ(-1) |∑_{n ≤ N} ψ(n) w(n)|² = 0`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L40-L63
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L40-L63

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.parseval_twisted (w : ℕ → ℤ) :
    ∑ ψ : DirichletCharacter ℂ p,
        ψ (-1) * (((‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 : ℝ)) : ℂ) = 0 := by sorry
