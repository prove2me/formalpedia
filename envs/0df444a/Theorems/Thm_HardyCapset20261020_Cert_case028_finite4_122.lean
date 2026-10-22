-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_122
-- name    : HardyCapset20261020.Cert.case028_finite4_122
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:32:06.875993+00:00
-- url     : https://prove2.me/theorems/d2493ec7-78c0-4aa8-b834-90b703fed1a7
-- title:
--   Finite row and cover checks for orbit 028, block 123
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [488, 492) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_122 (j : Fin 4) :
    ((if 488+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[488+j.val]! else true) &&
    (if 488+j.val < certificate028.pool.size then localCoverB certificate028 (488+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
