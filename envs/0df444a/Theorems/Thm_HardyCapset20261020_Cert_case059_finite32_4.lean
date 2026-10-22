-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case059_finite32_4
-- name    : HardyCapset20261020.Cert.case059_finite32_4
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:37:44.431762+00:00
-- url     : https://prove2.me/theorems/d0abac72-9ca8-495f-a942-b5c79003922a
-- title:
--   Finite row and cover checks for orbit 059, block 5
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [128, 160) for the original orbit 059 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate05920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case059_finite32_4 (j : Fin 32) :
    ((if 128+j.val < certificate059.rows.size then rowB certificate059 certificate059.rows[128+j.val]! else true) &&
    (if 128+j.val < certificate059.pool.size then localCoverB certificate059 (128+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
