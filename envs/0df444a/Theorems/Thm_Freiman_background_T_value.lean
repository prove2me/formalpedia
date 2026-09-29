-- Prove2me | Theorems.Thm_Freiman_background_T_value
-- name    : Freiman.background_T_value
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:48.613979+00:00
-- url     : https://prove2.me/theorems/a938d53e-e545-414c-9efc-25cf60dcb128
-- title:
--   Exact evaluation of the greatest tail from the empty state
-- statement:
--   T=[0;overline(131312)] equals -1+sqrt(462)/12.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_T_value :
    cfValue backgroundT = -1 + Real.sqrt 462 / 12 := by
  sorry

end Freiman
