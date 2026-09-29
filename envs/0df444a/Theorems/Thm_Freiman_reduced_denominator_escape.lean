-- Prove2me | Theorems.Thm_Freiman_reduced_denominator_escape
-- name    : Freiman.reduced_denominator_escape
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:21.427318+00:00
-- url     : https://prove2.me/theorems/a0c1d681-8e17-40cf-b348-cf091065c83e
-- title:
--   Reduced nearest denominators tend to infinity
-- statement:
--   Nearest rational approximations converge to ξ. Only finitely many reduced fractions of bounded denominator lie in a fixed bounded interval, so their reduced denominators escape every bound.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, proof of found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem reduced_denominator_escape (ξ : ℝ) (hξ : Irrational ξ) :
    ∀ R : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → R ≤ reducedApproximationDenominator ξ q := by
  sorry

end Freiman
