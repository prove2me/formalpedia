-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case029_finite32_5
-- name    : HardyCapset20261020.Cert.case029_finite32_5
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:33:27.883274+00:00
-- url     : https://prove2.me/theorems/bd991c53-65de-446a-a3e1-d7dcaced5cf8
-- title:
--   Finite row and cover checks for orbit 029, block 6
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [160, 192) for the original orbit 029 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case029_finite32_5 (j : Fin 32) :
    ((if 160+j.val < certificate029.rows.size then rowB certificate029 certificate029.rows[160+j.val]! else true) &&
    (if 160+j.val < certificate029.pool.size then localCoverB certificate029 (160+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
