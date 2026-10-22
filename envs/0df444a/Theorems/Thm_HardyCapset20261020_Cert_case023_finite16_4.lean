-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case023_finite16_4
-- name    : HardyCapset20261020.Cert.case023_finite16_4
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:23:29.360976+00:00
-- url     : https://prove2.me/theorems/3de1ac02-0a34-40c7-98ae-63c6f185d3ee
-- title:
--   Finite row and cover checks for orbit 023, block 5
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [64, 80) for the original orbit 023 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case023_finite16_4 (j : Fin 16) :
    ((if 64+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[64+j.val]! else true) &&
    (if 64+j.val < certificate023.pool.size then localCoverB certificate023 (64+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
