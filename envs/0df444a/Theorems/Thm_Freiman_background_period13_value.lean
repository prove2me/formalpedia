-- Prove2me | Theorems.Thm_Freiman_background_period13_value
-- name    : Freiman.background_period13_value
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:53.888926+00:00
-- url     : https://prove2.me/theorems/37cb4777-7a70-4888-b4c6-3864c9c3aaab
-- title:
--   Evaluation of the periodic continued fraction with period 13
-- statement:
--   The periodic tail [0;overline(1,3)] is exactly (sqrt(21)-3)/2.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_period13_value :
    cfValue backgroundPeriod13 = (Real.sqrt 21 - 3) / 2 := by
  sorry

end Freiman
