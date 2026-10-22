-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case173_finite32_12
-- name    : HardyCapset20261020.Cert.case173_finite32_12
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:13:29.4819+00:00
-- url     : https://prove2.me/theorems/3d8861c2-4e30-4825-93c7-827506bc187a
-- title:
--   Finite row and cover checks for orbit 173, block 13
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [384, 416) for the original orbit 173 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case173_finite32_12 (j : Fin 32) :
    ((if 384+j.val < certificate173.rows.size then rowB certificate173 certificate173.rows[384+j.val]! else true) &&
    (if 384+j.val < certificate173.pool.size then localCoverB certificate173 (384+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
