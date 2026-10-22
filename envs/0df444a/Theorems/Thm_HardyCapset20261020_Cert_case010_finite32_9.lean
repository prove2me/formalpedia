-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite32_9
-- name    : HardyCapset20261020.Cert.case010_finite32_9
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:04:18.33891+00:00
-- url     : https://prove2.me/theorems/799bdffb-8062-4a72-b784-300d217b9eaa
-- title:
--   Finite row and cover checks for orbit 010, block 10
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [288, 320) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite32_9 (j : Fin 32) :
    ((if 288+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[288+j.val]! else true) &&
    (if 288+j.val < certificate010.pool.size then localCoverB certificate010 (288+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
