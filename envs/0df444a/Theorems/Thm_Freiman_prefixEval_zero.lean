-- Prove2me | Theorems.Thm_Freiman_prefixEval_zero
-- name    : Freiman.prefixEval_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:37.052541+00:00
-- url     : https://prove2.me/theorems/56e9d989-8a2d-4bba-9aa3-a2ea50ada55e
-- title:
--   Zero tail equals the existing finite fraction
-- statement:
--   Evaluating a finite prefix at tail zero gives exactly the existing finiteCF definition.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, printed p. 7, equations found:continuants and found:continuity and the finite-tail paragraph after found:local-values; §1.2, Theorem 1.3 for the Perron/local comparison.

import Definitions.Def_Freiman_prefixEval

namespace Freiman

theorem prefixEval_zero (w : List ℕ+) : prefixEval w 0 = finiteCF w := by
  sorry

end Freiman
