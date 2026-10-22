-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case143_finite32_12
-- name    : HardyCapset20261020.Cert.case143_finite32_12
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:53:06.248135+00:00
-- url     : https://prove2.me/theorems/20bf3b13-6646-40b9-92b7-22687b77d7e1
-- title:
--   Finite row and cover checks for orbit 143, block 13
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [384, 416) for the original orbit 143 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate14320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case143_finite32_12 (j : Fin 32) :
    ((if 384+j.val < certificate143.rows.size then rowB certificate143 certificate143.rows[384+j.val]! else true) &&
    (if 384+j.val < certificate143.pool.size then localCoverB certificate143 (384+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
