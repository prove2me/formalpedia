-- Prove2me | Theorems.Thm_K230_thm230_iff_KPrimeOrdIR
-- name    : K230.thm230_iff_KPrimeOrdIR
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T21:15:27.03209+00:00
-- url     : https://prove2.me/theorems/2e7e4dac-1b83-4aae-938a-30bf1873395e
-- title:
--   K230: numerical derivability iff K+IR inconsistency
-- statement:
--   The falsity code $1$ is derivable in the numerical calculus if and only if the compact theory $K' + \mathrm{IR}$ (`KPrimeOrdIR`) proves a contradiction in classical first-order logic. This is `thm230_iff_KPrimeOrdIR` in `Bridge230.v`, the numerical decoding bridge.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/logic/Bridge230.v

import Definitions.Def_K230_calculus
import Definitions.Def_K230_theoryK
import Definitions.Def_K230_nd
import Definitions.Def_K230_fol

namespace K230
theorem thm230_iff_KPrimeOrdIR : Thm230 1 ↔ TPrv KPrimeOrdIR bot := by sorry
end K230
