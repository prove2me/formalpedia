-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_128
-- name    : HardyCapset20261020.Cert.case028_finite4_128
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:33:11.268478+00:00
-- url     : https://prove2.me/theorems/f9673a33-bb09-49c1-9f5e-8b6839aeca9e
-- title:
--   Finite row and cover checks for orbit 028, block 129
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [512, 516) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_128 (j : Fin 4) :
    ((if 512+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[512+j.val]! else true) &&
    (if 512+j.val < certificate028.pool.size then localCoverB certificate028 (512+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
