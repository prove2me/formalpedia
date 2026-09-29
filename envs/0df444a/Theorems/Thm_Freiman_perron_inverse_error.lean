-- Prove2me | Theorems.Thm_Freiman_perron_inverse_error
-- name    : Freiman.perron_inverse_error
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:11.529043+00:00
-- url     : https://prove2.me/theorems/50730738-6fa7-4f8e-a813-2c49b1735d0f
-- title:
--   Exact Perron inverse-error identity
-- statement:
--   The report’s Perron identity with count indexing: perronValue b n uses the digit b n and the convergent with exactly n preceding digits. The n=0 case uses p_0=0,q_0=1.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem perron_inverse_error (b : ℕ → ℕ+) (n : ℕ) :
    1 / ((continuantQ b n : ℝ) *
      |(continuantQ b n : ℝ) * cfValue b - (continuantP b n : ℝ)|) = perronValue b n := by
  sorry

end Freiman
