-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_79
-- name    : HardyCapset20261020.Cert.case028_finite4_79
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:23:23.680422+00:00
-- url     : https://prove2.me/theorems/de283ec9-a228-48ce-957c-2fd7753bed21
-- title:
--   Finite row and cover checks for orbit 028, block 80
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [316, 320) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_79 (j : Fin 4) :
    ((if 316+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[316+j.val]! else true) &&
    (if 316+j.val < certificate028.pool.size then localCoverB certificate028 (316+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
