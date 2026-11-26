-- Prove2me | Theorems.Thm_MellinDuality_sum_oddChars_eq_sum
-- name    : MellinDuality.sum_oddChars_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:47.022171+00:00
-- url     : https://prove2.me/theorems/248ce8b7-180f-4ee7-b601-966946b83a4d
-- title:
--   Mellin Duality: sum odd Chars eq sum
-- statement:
--   Only odd characters contribute: for even `ψ`, `𝒢(ψ̄) = 0`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L206-L214
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean#L206-L214

module
public import Definitions.Def_MellinDuality_Half
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.sum_oddChars_eq_sum (F : DirichletCharacter ℂ p → ℂ)
    (hF : ∀ ψ : DirichletCharacter ℂ p, ψ (-1) = 1 → F ψ = 0) :
    ∑ ψ ∈ oddChars p, F ψ = ∑ ψ, F ψ := by sorry
