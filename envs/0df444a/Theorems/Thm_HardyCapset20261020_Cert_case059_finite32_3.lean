-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case059_finite32_3
-- name    : HardyCapset20261020.Cert.case059_finite32_3
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:37:42.431219+00:00
-- url     : https://prove2.me/theorems/f55f3681-bbc8-42d2-b0d1-89b342ff71c9
-- title:
--   Finite row and cover checks for orbit 059, block 4
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [96, 128) for the original orbit 059 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate05920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case059_finite32_3 (j : Fin 32) :
    ((if 96+j.val < certificate059.rows.size then rowB certificate059 certificate059.rows[96+j.val]! else true) &&
    (if 96+j.val < certificate059.pool.size then localCoverB certificate059 (96+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
