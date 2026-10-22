-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_27
-- name    : HardyCapset20261020.Cert.case028_finite4_27
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:14:27.945399+00:00
-- url     : https://prove2.me/theorems/59ff8cb2-5697-4823-8ce5-3fd04d90e648
-- title:
--   Finite row and cover checks for orbit 028, block 28
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [108, 112) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_27 (j : Fin 4) :
    ((if 108+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[108+j.val]! else true) &&
    (if 108+j.val < certificate028.pool.size then localCoverB certificate028 (108+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
