-- Prove2me | Theorems.Thm_Freiman_perron_arbitrary_error_control
-- name    : Freiman.perron_arbitrary_error_control
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:27.098467+00:00
-- url     : https://prove2.me/theorems/ab94dcd5-2896-45ca-bb30-e584b2971715
-- title:
--   Every sufficiently late inverse error is controlled by late Perron values
-- statement:
--   Reduce the nearest rational p/q. A nonconvergent inverse error is at most 2 by Legendre. A convergent inverse error is a Perron value, and the factor from a common divisor is at most one. Escape of reduced denominators excludes all finitely many early convergents.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, proof of found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem perron_arbitrary_error_control (b : ℕ → ℕ+) :
    ∀ K : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      approximationValue (cfValue b) (q + 1) ≤ 2 ∨
      ∃ n : ℕ, K ≤ n ∧ approximationValue (cfValue b) (q + 1) ≤ perronValue b n := by
  sorry

end Freiman
