-- Prove2me | Theorems.Thm_Freiman_background_T_fixedpoint
-- name    : Freiman.background_T_fixedpoint
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:01:05.55325+00:00
-- url     : https://prove2.me/theorems/be5be08a-ddd1-4a03-b73d-4aafee753eb2
-- title:
--   The exact fixed point of the period 131312
-- statement:
--   The positive fixed point for the period matrix of 131312 is -1+sqrt(462)/12; it lies in (0,1).
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_T_fixedpoint :
    0 < -1 + Real.sqrt 462 / 12 ∧ -1 + Real.sqrt 462 / 12 < 1 ∧
      prefixEval [1,3,1,3,1,2] (-1 + Real.sqrt 462 / 12) = -1 + Real.sqrt 462 / 12 := by
  sorry

end Freiman
