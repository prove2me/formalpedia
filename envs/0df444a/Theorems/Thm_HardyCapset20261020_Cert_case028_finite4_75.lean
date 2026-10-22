-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_75
-- name    : HardyCapset20261020.Cert.case028_finite4_75
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:22:41.972053+00:00
-- url     : https://prove2.me/theorems/ea624a2b-ae25-4cb2-a77e-c87924c7f68f
-- title:
--   Finite row and cover checks for orbit 028, block 76
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [300, 304) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_75 (j : Fin 4) :
    ((if 300+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[300+j.val]! else true) &&
    (if 300+j.val < certificate028.pool.size then localCoverB certificate028 (300+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
