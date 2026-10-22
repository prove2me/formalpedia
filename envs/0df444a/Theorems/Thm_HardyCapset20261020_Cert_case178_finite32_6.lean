-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case178_finite32_6
-- name    : HardyCapset20261020.Cert.case178_finite32_6
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:19:47.489596+00:00
-- url     : https://prove2.me/theorems/444648db-93e1-4d1e-ad85-ab31e272964c
-- title:
--   Finite row and cover checks for orbit 178, block 7
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [192, 224) for the original orbit 178 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case178_finite32_6 (j : Fin 32) :
    ((if 192+j.val < certificate178.rows.size then rowB certificate178 certificate178.rows[192+j.val]! else true) &&
    (if 192+j.val < certificate178.pool.size then localCoverB certificate178 (192+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
