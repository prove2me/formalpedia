-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case178_finite32_2
-- name    : HardyCapset20261020.Cert.case178_finite32_2
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:19:05.236054+00:00
-- url     : https://prove2.me/theorems/897f7d50-44de-49f3-b605-8782637838f7
-- title:
--   Finite row and cover checks for orbit 178, block 3
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [64, 96) for the original orbit 178 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case178_finite32_2 (j : Fin 32) :
    ((if 64+j.val < certificate178.rows.size then rowB certificate178 certificate178.rows[64+j.val]! else true) &&
    (if 64+j.val < certificate178.pool.size then localCoverB certificate178 (64+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
