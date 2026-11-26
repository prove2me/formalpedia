-- Prove2me | Theorems.Thm_MellinDuality_second_moment_re
-- name    : MellinDuality.second_moment_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:10.184656+00:00
-- url     : https://prove2.me/theorems/214da990-aa55-5d97-a457-a09d6fdf1d98
-- title:
--   Mellin Duality: second moment re
-- statement:
--   **Second moments over the family** (Proposition 4.2 of Paper II):
--   `∑_{a ∈ H} (Re 𝒞(a))² = ∑_{d ∈ H} M(d) M(d²)` with `M(d) = ∑_{u ∈ H} s(u) s(d u)`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L314-L357
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L314-L357

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

theorem MellinDuality.second_moment_re :
    ∑ a ∈ fiber χ 1, (fam χ 2 a).re ^ 2 =
      ∑ d ∈ fiber χ 1, multCorr (fiber χ 1) d * multCorr (fiber χ 1) (d ^ 2) := by sorry
