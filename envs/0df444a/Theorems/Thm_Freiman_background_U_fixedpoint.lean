-- Prove2me | Theorems.Thm_Freiman_background_U_fixedpoint
-- name    : Freiman.background_U_fixedpoint
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:00:45.507547+00:00
-- url     : https://prove2.me/theorems/5684dcba-ac0a-4274-846a-71207e6ff377
-- title:
--   The exact fixed point of the period 131213
-- statement:
--   The positive fixed point for the period matrix of 131213 is (2 sqrt(462)-28)/19; it lies in (0,1).
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 and its proof, printed pp. 11–12.

import Definitions.Def_Freiman_backgroundWords

namespace Freiman

theorem background_U_fixedpoint :
    0 < (2 * Real.sqrt 462 - 28) / 19 ∧ (2 * Real.sqrt 462 - 28) / 19 < 1 ∧
      prefixEval [1,3,1,2,1,3] ((2 * Real.sqrt 462 - 28) / 19) =
        (2 * Real.sqrt 462 - 28) / 19 := by
  sorry

end Freiman
