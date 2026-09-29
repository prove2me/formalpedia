-- Prove2me | Theorems.Thm_Freiman_upper_rows_normal
-- name    : Freiman.upper_rows_normal
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:29.270262+00:00
-- url     : https://prove2.me/theorems/8b296f37-93c4-4e50-a374-6aac1deb7bc3
-- title:
--   All five prefix images are normal deletions
-- statement:
--   The five prescribed split types are normal for every continued-fraction prefix and its actual parity.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_rows_normal (w : List ℕ+) (i : Fin 5) :
    let D := upperImageSplit w (upperRows i); upperNormalSplit D.parent D.left D.right := by
  sorry

end Freiman
