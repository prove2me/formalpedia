-- Prove2me | Theorems.Thm_MellinDuality_second_moment_im
-- name    : MellinDuality.second_moment_im
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:52.840147+00:00
-- url     : https://prove2.me/theorems/b41a6e5b-88b3-4ab6-984a-0e2d741d6a4e
-- title:
--   Mellin Duality: second moment im
-- statement:
--   **Second moments over the family** (Proposition 4.2 of Paper II):
--   `∑_{a ∈ H} (Im 𝒞(a))² = ∑_{d ∈ H} M_{2H}(d) M(d²)`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L361-L414
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L361-L414

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

theorem MellinDuality.second_moment_im :
    ∑ a ∈ fiber χ 1, (fam χ 2 a).im ^ 2 =
      ∑ d ∈ fiber χ 1, multCorr (fiber χ gi) d * multCorr (fiber χ 1) (d ^ 2) := by sorry
