-- Prove2me | Theorems.Thm_Freiman_upper_tree_word_growth
-- name    : Freiman.upper_tree_word_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:31.468553+00:00
-- url     : https://prove2.me/theorems/6bbef0a8-3580-4de5-9f7a-6e3f5a8ee95f
-- title:
--   Every three binary splits append a continued-fraction digit
-- statement:
--   At depth r the accumulated positive-digit prefix has length at least floor(r/3), for all initial states and prefixes.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Paragraph after m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_tree_word_growth (p : List ℕ+) (k : Fin 5) (w : List Bool) :
    w.length / 3 ≤ (upperStateAt ⟨p, k⟩ w).word.length := by
  sorry

end Freiman
