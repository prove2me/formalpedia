-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite32_11
-- name    : HardyCapset20261020.Cert.case010_finite32_11
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:04:22.028991+00:00
-- url     : https://prove2.me/theorems/8937fb6e-0feb-4086-bf7a-31444345ad06
-- title:
--   Finite row and cover checks for orbit 010, block 12
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [352, 384) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite32_11 (j : Fin 32) :
    ((if 352+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[352+j.val]! else true) &&
    (if 352+j.val < certificate010.pool.size then localCoverB certificate010 (352+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
