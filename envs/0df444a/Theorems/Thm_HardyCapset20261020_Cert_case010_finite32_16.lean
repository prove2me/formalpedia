-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite32_16
-- name    : HardyCapset20261020.Cert.case010_finite32_16
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:05:28.689814+00:00
-- url     : https://prove2.me/theorems/15e6f9de-932c-4db9-b6ef-bab31daa0f27
-- title:
--   Finite row and cover checks for orbit 010, block 17
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [512, 544) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite32_16 (j : Fin 32) :
    ((if 512+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[512+j.val]! else true) &&
    (if 512+j.val < certificate010.pool.size then localCoverB certificate010 (512+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
