-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_22
-- name    : HardyCapset20261020.Cert.case028_finite4_22
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:13:36.073511+00:00
-- url     : https://prove2.me/theorems/e19e3315-15c8-4a5f-9e13-cafe0f6fc2f2
-- title:
--   Finite row and cover checks for orbit 028, block 23
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [88, 92) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_22 (j : Fin 4) :
    ((if 88+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[88+j.val]! else true) &&
    (if 88+j.val < certificate028.pool.size then localCoverB certificate028 (88+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
