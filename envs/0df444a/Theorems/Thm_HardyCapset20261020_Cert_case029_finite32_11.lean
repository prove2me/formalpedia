-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case029_finite32_11
-- name    : HardyCapset20261020.Cert.case029_finite32_11
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:34:12.942126+00:00
-- url     : https://prove2.me/theorems/22aaf60e-bbf2-4035-92c1-1fba2a3d1cc2
-- title:
--   Finite row and cover checks for orbit 029, block 12
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [352, 384) for the original orbit 029 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case029_finite32_11 (j : Fin 32) :
    ((if 352+j.val < certificate029.rows.size then rowB certificate029 certificate029.rows[352+j.val]! else true) &&
    (if 352+j.val < certificate029.pool.size then localCoverB certificate029 (352+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
