-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case178_finite32_10
-- name    : HardyCapset20261020.Cert.case178_finite32_10
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:20:20.58198+00:00
-- url     : https://prove2.me/theorems/cef1a3db-2544-4681-8408-6c753369961c
-- title:
--   Finite row and cover checks for orbit 178, block 11
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [320, 352) for the original orbit 178 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case178_finite32_10 (j : Fin 32) :
    ((if 320+j.val < certificate178.rows.size then rowB certificate178 certificate178.rows[320+j.val]! else true) &&
    (if 320+j.val < certificate178.pool.size then localCoverB certificate178 (320+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
