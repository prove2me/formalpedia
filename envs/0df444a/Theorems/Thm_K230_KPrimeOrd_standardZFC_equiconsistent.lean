-- Prove2me | Theorems.Thm_K230_KPrimeOrd_standardZFC_equiconsistent
-- name    : K230.KPrimeOrd_standardZFC_equiconsistent
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T21:15:44.7681+00:00
-- url     : https://prove2.me/theorems/22b3911b-9785-4d2b-9ed9-ac59913c3fed
-- title:
--   K230: K equiconsistent with ZFC
-- statement:
--   The compact theory $K'$ (`KPrimeOrd`) is inconsistent if and only if standard ZFC is inconsistent. This is `KPrimeOrd_standardZFC_equiconsistent` in `KUpperConsistency.v`.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/settheory/KUpperConsistency.v

import Definitions.Def_K230_theoryK
import Definitions.Def_K230_zfc
import Definitions.Def_K230_nd
import Definitions.Def_K230_fol

namespace K230
theorem KPrimeOrd_standardZFC_equiconsistent : TPrv KPrimeOrd bot ↔ TPrv StandardZFC bot := by sorry
end K230
