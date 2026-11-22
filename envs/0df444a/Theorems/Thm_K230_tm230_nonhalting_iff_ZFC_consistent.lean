-- Prove2me | Theorems.Thm_K230_tm230_nonhalting_iff_ZFC_consistent
-- name    : K230.tm230_nonhalting_iff_ZFC_consistent
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T21:16:04.364826+00:00
-- url     : https://prove2.me/theorems/3602f898-9ee7-4e33-9539-9d3bb5db5cff
-- title:
--   K230: nonhalting iff ZFC consistency
-- statement:
--   The machine K230 does not halt from the blank tape if and only if standard ZFC is consistent (does not prove a contradiction). This is the corollary `tm230_nonhalting_iff_ZFC_consistent` in `Correct230.v`.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/tm/Correct230.v

import Definitions.Def_K230_tm
import Definitions.Def_K230_zfc
import Definitions.Def_K230_nd
import Definitions.Def_K230_fol

namespace K230
theorem tm230_nonhalting_iff_ZFC_consistent : (¬ Halts c0) ↔ (¬ TPrv StandardZFC bot) := by sorry
end K230
