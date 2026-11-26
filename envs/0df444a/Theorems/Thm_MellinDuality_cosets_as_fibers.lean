-- Prove2me | Theorems.Thm_MellinDuality_cosets_as_fibers
-- name    : MellinDuality.cosets_as_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:00:19.898047+00:00
-- url     : https://prove2.me/theorems/62b52a26-bed6-4540-b2d7-e4a3b7f3f226
-- title:
--   Mellin Duality: cosets as fibers
-- statement:
--   **The cosets** (Paper II, §2). At `p ≡ 5 (mod 8)` a quartic `χ` is odd, its fibre over `1` is
--   the group `H` of nonzero fourth powers, and if `χ(2) = i` its fibre over `i` is `2H`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L105-L108
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L105-L108

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.cosets_as_fibers {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 5) (hχ : orderOf χ = 4) :
    χ (-1) = -1 ∧ fiber χ 1 = univ.filter (fun x : ZMod p => x ≠ 0 ∧ ∃ y, y ^ 4 = x) ∧
      (χ 2 = gi → fiber χ gi = (fiber χ 1).image (2 * ·)) := by sorry
