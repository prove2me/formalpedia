-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case016_finite32_9
-- name    : HardyCapset20261020.Cert.case016_finite32_9
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:51:18.492994+00:00
-- url     : https://prove2.me/theorems/0e1be53f-4810-4f75-a7db-a0d36747d658
-- title:
--   Finite row and cover checks for orbit 016, block 10
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [288, 320) for the original orbit 016 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01620261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case016_finite32_9 (j : Fin 32) :
    ((if 288+j.val < certificate016.rows.size then rowB certificate016 certificate016.rows[288+j.val]! else true) &&
    (if 288+j.val < certificate016.pool.size then localCoverB certificate016 (288+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
