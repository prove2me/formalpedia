-- Prove2me | Theorems.Thm_MellinDuality_gcd_decomposition
-- name    : MellinDuality.gcd_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:02:09.059555+00:00
-- url     : https://prove2.me/theorems/3fc6bf4f-f170-4b99-bd0c-b28ebd07144a
-- title:
--   Mellin Duality: gcd decomposition
-- statement:
--   **The gcd decomposition** (proof of Proposition 6.3): every `(n, n') ∈ [1, N]²` is `(ar, br)` for
--   one coprime `(a, b)` and one `r ≤ ⌊N / max(a, b)⌋`.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L168-L171
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/Solution.lean#L168-L171

module
public import Definitions.Def_MellinDuality
public import Definitions.Def_MellinDuality_Solution
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.gcd_decomposition {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, F n n' =
      ∑ ab ∈ coprimePairs N, ∑ r ∈ pairRange N ab, F (ab.1 * r) (ab.2 * r) := by sorry
