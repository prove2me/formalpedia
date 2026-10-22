-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case016_finite32_12
-- name    : HardyCapset20261020.Cert.case016_finite32_12
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:51:47.033809+00:00
-- url     : https://prove2.me/theorems/77625646-b938-402b-bde4-261132b357f0
-- title:
--   Finite row and cover checks for orbit 016, block 13
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [384, 416) for the original orbit 016 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01620261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case016_finite32_12 (j : Fin 32) :
    ((if 384+j.val < certificate016.rows.size then rowB certificate016 certificate016.rows[384+j.val]! else true) &&
    (if 384+j.val < certificate016.pool.size then localCoverB certificate016 (384+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
