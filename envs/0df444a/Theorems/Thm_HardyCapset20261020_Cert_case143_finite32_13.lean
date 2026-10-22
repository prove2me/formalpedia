-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case143_finite32_13
-- name    : HardyCapset20261020.Cert.case143_finite32_13
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:53:13.656065+00:00
-- url     : https://prove2.me/theorems/f7d5ada0-b275-49d1-945a-eb7baf5bf95b
-- title:
--   Finite row and cover checks for orbit 143, block 14
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [416, 448) for the original orbit 143 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate14320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case143_finite32_13 (j : Fin 32) :
    ((if 416+j.val < certificate143.rows.size then rowB certificate143 certificate143.rows[416+j.val]! else true) &&
    (if 416+j.val < certificate143.pool.size then localCoverB certificate143 (416+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
