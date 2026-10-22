-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite32_0
-- name    : HardyCapset20261020.Cert.case010_finite32_0
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:02:22.049243+00:00
-- url     : https://prove2.me/theorems/b134a55c-27fe-4c93-bc57-cf8e55d39fa4
-- title:
--   Finite row and cover checks for orbit 010, block 1
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [0, 32) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite32_0 (j : Fin 32) :
    ((if 0+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[0+j.val]! else true) &&
    (if 0+j.val < certificate010.pool.size then localCoverB certificate010 (0+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
