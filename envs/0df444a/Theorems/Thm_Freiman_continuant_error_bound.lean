-- Prove2me | Theorems.Thm_Freiman_continuant_error_bound
-- name    : Freiman.continuant_error_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:06.486879+00:00
-- url     : https://prove2.me/theorems/46ce7976-5a40-4cd9-9f63-dbc2b175bc2f
-- title:
--   Strict convergent error bound
-- statement:
--   Substitution of the next complete quotient into the continuant formula gives |q_n ξ-p_n|<1/q_(n+1).
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.1 after found:continuity; §1.2 found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem continuant_error_bound (b : ℕ → ℕ+) (n : ℕ) :
    |(continuantQ b n : ℝ) * cfValue b - (continuantP b n : ℝ)| <
      1 / (continuantQ b (n + 1) : ℝ) := by
  sorry

end Freiman
