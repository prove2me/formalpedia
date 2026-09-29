-- Prove2me | Theorems.Thm_Freiman_perron_frequently_at_least_two
-- name    : Freiman.perron_frequently_at_least_two
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:14.447929+00:00
-- url     : https://prove2.me/theorems/69b125aa-9466-422c-b3eb-ae160485b58f
-- title:
--   Perron values have limsup at least two
-- statement:
--   If digits at least two occur infinitely often, P_n exceeds those digits. Otherwise the eventual all-one tail gives P_n→sqrt 5>2, by the report’s cylinder continuity argument.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, proof of found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem perron_frequently_at_least_two (b : ℕ → ℕ+) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 2 - ε < perronValue b n := by
  sorry

end Freiman
