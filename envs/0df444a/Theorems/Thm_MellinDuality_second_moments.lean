-- Prove2me | Theorems.Thm_MellinDuality_second_moments
-- name    : MellinDuality.second_moments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:01:51.530577+00:00
-- url     : https://prove2.me/theorems/f4f5cb9f-5915-4597-83d2-e5dc47f80b89
-- title:
--   Mellin Duality: second moments
-- statement:
--   **Second moments over the family** (Proposition 4.2):
--   `∑_{a ∈ H} (Re 𝒞(a))² = ∑_{d ∈ H} M(d) M(d²)` and `∑_{a ∈ H} (Im 𝒞(a))² = ∑_{d ∈ H} M_{F_i}(d) M(d²)`,
--   with `F_i` the fibre over `i` (`2H` when `χ(2) = i`).
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L159-L164
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L159-L164

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.second_moments {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    ∑ a ∈ fiber χ 1, (fam χ 2 a).re ^ 2 =
        ∑ d ∈ fiber χ 1, multCorr (fiber χ 1) d * multCorr (fiber χ 1) (d ^ 2) ∧
      ∑ a ∈ fiber χ 1, (fam χ 2 a).im ^ 2 =
        ∑ d ∈ fiber χ 1, multCorr (fiber χ gi) d * multCorr (fiber χ 1) (d ^ 2) := by sorry
