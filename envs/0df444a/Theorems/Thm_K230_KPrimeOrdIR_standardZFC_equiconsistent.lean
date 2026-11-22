-- Prove2me | Theorems.Thm_K230_KPrimeOrdIR_standardZFC_equiconsistent
-- name    : K230.KPrimeOrdIR_standardZFC_equiconsistent
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T21:15:34.429436+00:00
-- url     : https://prove2.me/theorems/93f82899-320d-41ea-afdc-8f4f108f8aec
-- title:
--   K230: K+IR equiconsistent with ZFC
-- statement:
--   The theory $K' + \mathrm{IR}$ is inconsistent if and only if standard ZFC is inconsistent. This is `KPrimeOrdIR_standardZFC_equiconsistent` in `KUpperConsistency.v`, combining the tagged-quotient interpretation (lower reduction) and constructible-hierarchy reflection (upper reduction).
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/settheory/KUpperConsistency.v

import Definitions.Def_K230_theoryK
import Definitions.Def_K230_zfc
import Definitions.Def_K230_nd
import Definitions.Def_K230_fol

namespace K230
theorem KPrimeOrdIR_standardZFC_equiconsistent : TPrv KPrimeOrdIR bot ↔ TPrv StandardZFC bot := by sorry
end K230
