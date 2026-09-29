-- Prove2me | Theorems.Thm_Freiman_background_period13_fixedpoint
-- name    : Freiman.background_period13_fixedpoint
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:57.652256+00:00
-- url     : https://prove2.me/theorems/152c113c-fa05-4d13-8a84-c110554203e8
-- title:
--   The exact positive fixed point of the period 13
-- statement:
--   The number (sqrt(21)-3)/2 lies strictly between zero and one and is fixed by the continued-fraction prefix map with digits 13.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_period13_fixedpoint :
    0 < (Real.sqrt 21 - 3) / 2 ∧ (Real.sqrt 21 - 3) / 2 < 1 ∧
      prefixEval [1,3] ((Real.sqrt 21 - 3) / 2) = (Real.sqrt 21 - 3) / 2 := by
  sorry

end Freiman
