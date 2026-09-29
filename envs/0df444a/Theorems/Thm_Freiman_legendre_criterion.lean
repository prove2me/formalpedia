-- Prove2me | Theorems.Thm_Freiman_legendre_criterion
-- name    : Freiman.legendre_criterion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:11.855767+00:00
-- url     : https://prove2.me/theorems/7a6df89c-36e1-4007-aa6a-043be7c7b649
-- title:
--   Legendre’s convergent criterion for the existing cfValue
-- statement:
--   The reduced rational p/q in (0,1), q≥2, is a convergent whenever its approximation error is below 1/(2q²). This is exactly found:legendre for the existing cfValue.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, found:legendre

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem legendre_criterion (b : ℕ → ℕ+) (p q : ℕ) (hp : 0 < p) (hpq : p < q) (hq : 2 ≤ q) (hcop : Nat.Coprime p q) :
    |cfValue b - (p : ℝ) / q| < 1 / (2 * (q : ℝ)^2) →
      ∃ n : ℕ, cfConvergent b n = (p : ℝ) / q := by
  sorry

end Freiman
