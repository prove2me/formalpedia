-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case029_finite32_3
-- name    : HardyCapset20261020.Cert.case029_finite32_3
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:32:52.804822+00:00
-- url     : https://prove2.me/theorems/bfa5ccbb-9cf8-47e5-897b-7db3cafd247b
-- title:
--   Finite row and cover checks for orbit 029, block 4
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [96, 128) for the original orbit 029 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case029_finite32_3 (j : Fin 32) :
    ((if 96+j.val < certificate029.rows.size then rowB certificate029 certificate029.rows[96+j.val]! else true) &&
    (if 96+j.val < certificate029.pool.size then localCoverB certificate029 (96+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
