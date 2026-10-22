-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite16_18
-- name    : HardyCapset20261020.Cert.case010_finite16_18
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:10:12.218+00:00
-- url     : https://prove2.me/theorems/6cf7d8b6-da7e-403b-8182-c10a766b2375
-- title:
--   Finite row and cover checks for orbit 010, block 19
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [288, 304) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite16_18 (j : Fin 16) :
    ((if 288+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[288+j.val]! else true) &&
    (if 288+j.val < certificate010.pool.size then localCoverB certificate010 (288+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
