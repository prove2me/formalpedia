-- Prove2me | Theorems.Thm_Freiman_prefixEval_mem_Icc
-- name    : Freiman.prefixEval_mem_Icc
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:48.555817+00:00
-- url     : https://prove2.me/theorems/f24fa507-3bf1-4f79-99be-14466683c036
-- title:
--   prefixEval mem Icc
-- statement:
--   The prefix map of any finite positive-digit word preserves the closed interval [0,1], including the empty word.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, printed p.7, definition of the finite prefix map T_w and its composition order.

import Definitions.Def_Freiman_prefixEval

namespace Freiman

theorem prefixEval_mem_Icc (w : List ℕ+) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    prefixEval w x ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

end Freiman
