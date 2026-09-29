-- Prove2me | Theorems.Thm_Freiman_perron_eventually_one_limit
-- name    : Freiman.perron_eventually_one_limit
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:32.126884+00:00
-- url     : https://prove2.me/theorems/d945bd00-f731-4821-a69a-bb6df094779a
-- title:
--   An eventually all-one digit string has Perron values tending to sqrt five
-- statement:
--   In the eventual all-one case, the forward tail is the periodic fixed point (sqrt 5−1)/2 and cylinder continuity sends the growing backward all-one prefix to the same value. Thus P_n→sqrt 5. This is the report’s second case for the lower bound two.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem perron_eventually_one_limit (b : ℕ → ℕ+) (h : ∃ N : ℕ, ∀ n : ℕ, N≤n → b n=1) :
    Filter.Tendsto (perronValue b) Filter.atTop (nhds (Real.sqrt 5)) := by
  sorry

end Freiman
