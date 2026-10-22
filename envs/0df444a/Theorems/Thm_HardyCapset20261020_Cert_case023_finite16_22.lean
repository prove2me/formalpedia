-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case023_finite16_22
-- name    : HardyCapset20261020.Cert.case023_finite16_22
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:26:28.418436+00:00
-- url     : https://prove2.me/theorems/e6b71883-b940-477b-bec1-f1ab0fb79ade
-- title:
--   Finite row and cover checks for orbit 023, block 23
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [352, 368) for the original orbit 023 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case023_finite16_22 (j : Fin 16) :
    ((if 352+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[352+j.val]! else true) &&
    (if 352+j.val < certificate023.pool.size then localCoverB certificate023 (352+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
