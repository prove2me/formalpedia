-- Prove2me | Theorems.Thm_MellinDuality_coset_lemma
-- name    : MellinDuality.coset_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:45:37.773628+00:00
-- url     : https://prove2.me/theorems/98d78800-4563-5e40-8317-51d98e4cffc8
-- title:
--   Mellin Duality: coset lemma
-- statement:
--   **Lemma 2.1 of Paper II.** `Re 𝒞(a) = ∑_{u ∈ H} s(u) s(a u²)` and
--   `Im 𝒞(a) = ∑_{u ∈ 2H} s(u) s(a u²)`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L152-L155
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L152-L155

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt}
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ

theorem MellinDuality.coset_lemma (a : ZMod p) :
    (fam χ 2 a).re = ∑ u ∈ fiber χ 1, parSign u * parSign (a * u ^ 2) ∧
      (fam χ 2 a).im = ∑ u ∈ fiber χ gi, parSign u * parSign (a * u ^ 2) := by sorry
