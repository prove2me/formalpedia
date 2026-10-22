-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case016_finite32_11
-- name    : HardyCapset20261020.Cert.case016_finite32_11
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:51:45.455671+00:00
-- url     : https://prove2.me/theorems/1b92bb24-650c-43c4-88aa-1e9f5eb56ec7
-- title:
--   Finite row and cover checks for orbit 016, block 12
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [352, 384) for the original orbit 016 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01620261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case016_finite32_11 (j : Fin 32) :
    ((if 352+j.val < certificate016.rows.size then rowB certificate016 certificate016.rows[352+j.val]! else true) &&
    (if 352+j.val < certificate016.pool.size then localCoverB certificate016 (352+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
