-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite16_22
-- name    : HardyCapset20261020.Cert.case010_finite16_22
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:10:51.563718+00:00
-- url     : https://prove2.me/theorems/e6874c68-35b7-4b10-a0d4-a74ba9d8574b
-- title:
--   Finite row and cover checks for orbit 010, block 23
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [352, 368) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite16_22 (j : Fin 16) :
    ((if 352+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[352+j.val]! else true) &&
    (if 352+j.val < certificate010.pool.size then localCoverB certificate010 (352+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
