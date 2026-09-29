-- Prove2me | Theorems.Thm_Freiman_upper_padding_converges
-- name    : Freiman.upper_padding_converges
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:14.241227+00:00
-- url     : https://prove2.me/theorems/883d1442-852d-43dd-81b1-aa8989be5e01
-- title:
--   Central heights converge under longer truncations padded by 3
-- statement:
--   The padded word agrees with the original on the full central window of radius j. The report’s cylinder continuity therefore makes its central height converge to that of the original word.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:completed-bounds and found:continuity.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_padding_converges (a : ℤ → ℕ+) :
    Filter.Tendsto (fun j => localValue (upperPad a j) 0) Filter.atTop (nhds (localValue a 0)) := by
  sorry

end Freiman
