-- Prove2me | Theorems.Thm_Freiman_rational_cf_finite_expansion
-- name    : Freiman.rational_cf_finite_expansion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:17.848183+00:00
-- url     : https://prove2.me/theorems/541f8edb-7c1f-405c-ad60-9bbd348188bd
-- title:
--   Reduced rationals have canonical finite expansions
-- statement:
--   The Euclidean algorithm gives the rational’s finite expansion with final digit at least two, including exact numerator and denominator equality.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, found:legendre

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem rational_cf_finite_expansion (p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q) :
    ∃ w : List ℕ+, w ≠ [] ∧
      2 ≤ ((w.getLastD 1 : ℕ+) : ℕ) ∧
      wordContinuantP w = p ∧ wordContinuantQ w = q := by
  sorry

end Freiman
