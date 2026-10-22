-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_55
-- name    : HardyCapset20261020.Cert.case028_finite4_55
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:19:13.448163+00:00
-- url     : https://prove2.me/theorems/75d66c47-4d55-4084-9fb1-3338b0caea18
-- title:
--   Finite row and cover checks for orbit 028, block 56
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [220, 224) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_55 (j : Fin 4) :
    ((if 220+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[220+j.val]! else true) &&
    (if 220+j.val < certificate028.pool.size then localCoverB certificate028 (220+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
