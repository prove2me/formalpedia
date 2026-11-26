-- Prove2me | Theorems.Thm_MellinDuality_fam_eq_fibers
-- name    : MellinDuality.fam_eq_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:12.156164+00:00
-- url     : https://prove2.me/theorems/d28eeb30-d37a-58d7-83fb-8a90f00e2211
-- title:
--   Mellin Duality: fam eq fibers
-- statement:
--   **Lemma 2.1 of Paper II** in one line: `𝒞(a) = ∑_{u ∈ H} s(u)s(au²) + i ∑_{u ∈ 2H} s(u)s(au²)`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L120-L148
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L120-L148

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

theorem MellinDuality.fam_eq_fibers (a : ZMod p) :
    fam χ 2 a = ⟨sqCorr (fiber χ 1) a, sqCorr (fiber χ gi) a⟩ := by sorry
