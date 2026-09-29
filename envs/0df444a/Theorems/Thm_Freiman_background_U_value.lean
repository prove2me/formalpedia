-- Prove2me | Theorems.Thm_Freiman_background_U_value
-- name    : Freiman.background_U_value
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:50.972546+00:00
-- url     : https://prove2.me/theorems/d1ebffc4-7eb3-4d4d-a48c-6d794ec1039c
-- title:
--   Exact evaluation of the greatest tail from state 3
-- statement:
--   U=[0;overline(131213)] equals (2 sqrt(462)-28)/19.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_U_value :
    cfValue backgroundU = (2 * Real.sqrt 462 - 28) / 19 := by
  sorry

end Freiman
