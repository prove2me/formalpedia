-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case017_finite32_0
-- name    : HardyCapset20261020.Cert.case017_finite32_0
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:55:02.216419+00:00
-- url     : https://prove2.me/theorems/47e5caa5-7b3b-4778-b2bd-92e90a9026d1
-- title:
--   Finite row and cover checks for orbit 017, block 1
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [0, 32) for the original orbit 017 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01720261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case017_finite32_0 (j : Fin 32) :
    ((if 0+j.val < certificate017.rows.size then rowB certificate017 certificate017.rows[0+j.val]! else true) &&
    (if 0+j.val < certificate017.pool.size then localCoverB certificate017 (0+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
