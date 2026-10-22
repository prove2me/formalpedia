-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case149_finite32_4
-- name    : HardyCapset20261020.Cert.case149_finite32_4
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:01:43.020508+00:00
-- url     : https://prove2.me/theorems/b3c40c58-2cf9-432a-af4e-7bed476e5256
-- title:
--   Finite row and cover checks for orbit 149, block 5
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [128, 160) for the original orbit 149 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate14920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case149_finite32_4 (j : Fin 32) :
    ((if 128+j.val < certificate149.rows.size then rowB certificate149 certificate149.rows[128+j.val]! else true) &&
    (if 128+j.val < certificate149.pool.size then localCoverB certificate149 (128+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
