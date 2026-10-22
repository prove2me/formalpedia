-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_40
-- name    : HardyCapset20261020.Cert.case028_finite4_40
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:16:39.605239+00:00
-- url     : https://prove2.me/theorems/3aa1679c-b5d1-4e8d-b06d-5b5d23c4f970
-- title:
--   Finite row and cover checks for orbit 028, block 41
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [160, 164) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_40 (j : Fin 4) :
    ((if 160+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[160+j.val]! else true) &&
    (if 160+j.val < certificate028.pool.size then localCoverB certificate028 (160+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
