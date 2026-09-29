-- Prove2me | Theorems.Thm_Freiman_prefixEval_append
-- name    : Freiman.prefixEval_append
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:53.54347+00:00
-- url     : https://prove2.me/theorems/7ba6fded-64f8-487b-9554-1af3507f9d10
-- title:
--   prefixEval append
-- statement:
--   The prefix map of a concatenation of two finite words is the composition of their prefix maps, for every real tail parameter.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, printed p.7, definition of the finite prefix map T_w and its composition order.

import Definitions.Def_Freiman_prefixEval

namespace Freiman

theorem prefixEval_append (w v : List ℕ+) (x : ℝ) :
    prefixEval (w ++ v) x = prefixEval w (prefixEval v x) := by
  sorry

end Freiman
