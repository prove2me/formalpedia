-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case179_finite32_4
-- name    : HardyCapset20261020.Cert.case179_finite32_4
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:32:30.443992+00:00
-- url     : https://prove2.me/theorems/d007d5f2-188e-4ff6-ab3b-d0742c1ce754
-- title:
--   Finite row and cover checks for orbit 179, block 5
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [128, 160) for the original orbit 179 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case179_finite32_4 (j : Fin 32) :
    ((if 128+j.val < certificate179.rows.size then rowB certificate179 certificate179.rows[128+j.val]! else true) &&
    (if 128+j.val < certificate179.pool.size then localCoverB certificate179 (128+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
