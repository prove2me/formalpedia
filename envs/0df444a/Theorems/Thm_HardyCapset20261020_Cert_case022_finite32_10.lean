-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case022_finite32_10
-- name    : HardyCapset20261020.Cert.case022_finite32_10
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:02:11.180261+00:00
-- url     : https://prove2.me/theorems/91623fd7-1cd0-4264-9439-591e25fac254
-- title:
--   Finite row and cover checks for orbit 022, block 11
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [320, 352) for the original orbit 022 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02220261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case022_finite32_10 (j : Fin 32) :
    ((if 320+j.val < certificate022.rows.size then rowB certificate022 certificate022.rows[320+j.val]! else true) &&
    (if 320+j.val < certificate022.pool.size then localCoverB certificate022 (320+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
