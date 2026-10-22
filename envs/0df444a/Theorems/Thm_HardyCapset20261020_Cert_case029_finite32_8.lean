-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case029_finite32_8
-- name    : HardyCapset20261020.Cert.case029_finite32_8
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:34:04.095681+00:00
-- url     : https://prove2.me/theorems/7a970111-2738-4c63-a186-9cac64b9ec3f
-- title:
--   Finite row and cover checks for orbit 029, block 9
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [256, 288) for the original orbit 029 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case029_finite32_8 (j : Fin 32) :
    ((if 256+j.val < certificate029.rows.size then rowB certificate029 certificate029.rows[256+j.val]! else true) &&
    (if 256+j.val < certificate029.pool.size then localCoverB certificate029 (256+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
