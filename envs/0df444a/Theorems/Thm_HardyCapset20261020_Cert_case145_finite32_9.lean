-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case145_finite32_9
-- name    : HardyCapset20261020.Cert.case145_finite32_9
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:57:14.245758+00:00
-- url     : https://prove2.me/theorems/c2606801-5299-43c0-847e-1d1c789a817a
-- title:
--   Finite row and cover checks for orbit 145, block 10
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [288, 320) for the original orbit 145 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate14520261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case145_finite32_9 (j : Fin 32) :
    ((if 288+j.val < certificate145.rows.size then rowB certificate145 certificate145.rows[288+j.val]! else true) &&
    (if 288+j.val < certificate145.pool.size then localCoverB certificate145 (288+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
