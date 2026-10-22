-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_107
-- name    : HardyCapset20261020.Cert.case028_finite4_107
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:29:27.856216+00:00
-- url     : https://prove2.me/theorems/8befedf9-8839-4c88-b8b0-0c3a9b736a92
-- title:
--   Finite row and cover checks for orbit 028, block 108
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [428, 432) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_107 (j : Fin 4) :
    ((if 428+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[428+j.val]! else true) &&
    (if 428+j.val < certificate028.pool.size then localCoverB certificate028 (428+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
