-- Prove2me | Theorems.Thm_MellinDuality_coset_decomposition
-- name    : MellinDuality.coset_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:00:49.305237+00:00
-- url     : https://prove2.me/theorems/44dbf4f2-648d-4390-9ccc-e742046813d0
-- title:
--   Mellin Duality: coset decomposition
-- statement:
--   **Lemma 2.1.** `Re 𝒞(a) = ∑_{u ∈ H} s(u) s(au²)` and `Im 𝒞(a) = ∑_{u ∈ F_i} s(u) s(au²)`, where
--   `F_i` is the fibre of `χ` over `i` (which is `2H` when `χ(2) = i`).
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L112-L116
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L112-L116

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.coset_decomposition {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
    (a : ZMod p) :
    (fam χ 2 a).re = ∑ u ∈ fiber χ 1, parSign u * parSign (a * u ^ 2) ∧
      (fam χ 2 a).im = ∑ u ∈ fiber χ gi, parSign u * parSign (a * u ^ 2) := by sorry
