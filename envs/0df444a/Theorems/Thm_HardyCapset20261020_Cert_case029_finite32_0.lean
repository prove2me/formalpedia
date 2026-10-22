-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case029_finite32_0
-- name    : HardyCapset20261020.Cert.case029_finite32_0
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:32:43.739318+00:00
-- url     : https://prove2.me/theorems/7d7ae07e-bff3-4c0a-a329-6165e81b2ff6
-- title:
--   Finite row and cover checks for orbit 029, block 1
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [0, 32) for the original orbit 029 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case029_finite32_0 (j : Fin 32) :
    ((if 0+j.val < certificate029.rows.size then rowB certificate029 certificate029.rows[0+j.val]! else true) &&
    (if 0+j.val < certificate029.pool.size then localCoverB certificate029 (0+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
