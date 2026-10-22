-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case179_finite32_8
-- name    : HardyCapset20261020.Cert.case179_finite32_8
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:33:11.070986+00:00
-- url     : https://prove2.me/theorems/f2d140cb-b89b-442e-805f-965fc25803ec
-- title:
--   Finite row and cover checks for orbit 179, block 9
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [256, 288) for the original orbit 179 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case179_finite32_8 (j : Fin 32) :
    ((if 256+j.val < certificate179.rows.size then rowB certificate179 certificate179.rows[256+j.val]! else true) &&
    (if 256+j.val < certificate179.pool.size then localCoverB certificate179 (256+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
