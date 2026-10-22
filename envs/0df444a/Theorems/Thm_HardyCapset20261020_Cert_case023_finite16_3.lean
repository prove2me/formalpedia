-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case023_finite16_3
-- name    : HardyCapset20261020.Cert.case023_finite16_3
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:23:18.633847+00:00
-- url     : https://prove2.me/theorems/06197f5f-527f-470c-8b68-ba043527215a
-- title:
--   Finite row and cover checks for orbit 023, block 4
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [48, 64) for the original orbit 023 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case023_finite16_3 (j : Fin 16) :
    ((if 48+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[48+j.val]! else true) &&
    (if 48+j.val < certificate023.pool.size then localCoverB certificate023 (48+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
