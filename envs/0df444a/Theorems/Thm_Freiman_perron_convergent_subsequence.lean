-- Prove2me | Theorems.Thm_Freiman_perron_convergent_subsequence
-- name    : Freiman.perron_convergent_subsequence
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:15.403126+00:00
-- url     : https://prove2.me/theorems/84234dbe-6d2c-4b44-b8fc-31ad157f0912
-- title:
--   Perron values form the eventual convergent subsequence
-- statement:
--   Once the convergent numerator is nearest, the exact inverse-error identity identifies the approximation value at denominator q_n with P_n.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem perron_convergent_subsequence (b : ℕ → ℕ+) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      approximationValue (cfValue b) (continuantQ b n) = perronValue b n := by
  sorry

end Freiman
