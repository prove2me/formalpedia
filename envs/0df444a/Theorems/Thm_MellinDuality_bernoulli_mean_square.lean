-- Prove2me | Theorems.Thm_MellinDuality_bernoulli_mean_square
-- name    : MellinDuality.bernoulli_mean_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:43.534972+00:00
-- url     : https://prove2.me/theorems/0363657a-2a98-4d23-90ae-d00cfcda3387
-- title:
--   Mellin Duality: bernoulli mean square
-- statement:
--   **The Bernoulli mean square.** For an odd prime `p` and `a ≠ 0`,
--   `∑_{χ odd} |∑_{ψ odd} ψ(a) (1 - 2ψ̄(2)) (1 - 2χ(2)ψ(2)²) B_{1,ψ̄} B_{1,χψ²}|² = ((p - 1)/2)⁴`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L111-L148
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/MeanSquare.lean#L111-L148

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.bernoulli_mean_square (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    ∑ χ ∈ oddChars p, ‖∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
        (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2)‖ ^ 2 =
      (((p : ℝ) - 1) / 2) ^ 4 := by sorry
