-- Prove2me | Theorems.Thm_Freiman_gap_cylinder_decomposition
-- name    : Freiman.gap_cylinder_decomposition
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:41.846577+00:00
-- url     : https://prove2.me/theorems/4fb7dcf9-ed21-46c2-a05c-b93dd3657c76
-- title:
--   gap cylinder decomposition
-- statement:
--   The physical word match identifies the exact outward prefixes and both residual cfValue tails, including all shifts and reversals.
-- source:
--   Freiman Hall ray report, m3.tex; eq:m3:cylinder

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_cylinder_decomposition (a : ℤ → ℕ+) (i : ℤ) (s : GapState) (j : ℕ) (hm : gapMatch a i s) (hj : j < s.word.length) : localValue a (i+(j : ℤ)-(s.centre : ℤ)) = ((s.word[j]! : ℕ) : ℝ) + prefixEval ((s.word.take j).reverse) (cfValue (fun n : ℕ => a (i-(s.centre : ℤ)-(n : ℤ)-1))) + prefixEval (s.word.drop (j+1)) (cfValue (fun n : ℕ => a (i+(s.word.length : ℤ)-(s.centre : ℤ)+(n : ℤ)))) := by
  sorry

end Freiman
