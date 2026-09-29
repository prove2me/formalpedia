-- Prove2me | Theorems.Thm_Freiman_background_prefix12_radical
-- name    : Freiman.background_prefix12_radical
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:54.593693+00:00
-- url     : https://prove2.me/theorems/bddbfa0b-566d-452f-ba77-3c4464f010b1
-- title:
--   Exact evaluation of the prefix 12 applied to T
-- statement:
--   The two-digit prefix map T_12 evaluated at T gives (2 sqrt(462)-29)/19.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_prefix12_radical :
    prefixEval [1,2] (-1 + Real.sqrt 462 / 12) = (2 * Real.sqrt 462 - 29) / 19 := by
  sorry

end Freiman
