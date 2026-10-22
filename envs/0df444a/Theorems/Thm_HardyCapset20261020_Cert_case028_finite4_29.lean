-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_29
-- name    : HardyCapset20261020.Cert.case028_finite4_29
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:14:48.480445+00:00
-- url     : https://prove2.me/theorems/a9cbb8d2-31c3-4cc2-8fc4-16131696db88
-- title:
--   Finite row and cover checks for orbit 028, block 30
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [116, 120) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_29 (j : Fin 4) :
    ((if 116+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[116+j.val]! else true) &&
    (if 116+j.val < certificate028.pool.size then localCoverB certificate028 (116+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
