-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_12
-- name    : HardyCapset20261020.Cert.case028_finite4_12
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:11:53.439558+00:00
-- url     : https://prove2.me/theorems/5137560d-45fb-436b-b07b-1a3ef332e11b
-- title:
--   Finite row and cover checks for orbit 028, block 13
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [48, 52) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_12 (j : Fin 4) :
    ((if 48+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[48+j.val]! else true) &&
    (if 48+j.val < certificate028.pool.size then localCoverB certificate028 (48+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
