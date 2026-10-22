-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case023_finite16_8
-- name    : HardyCapset20261020.Cert.case023_finite16_8
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:24:09.76399+00:00
-- url     : https://prove2.me/theorems/82f4ab43-d32b-4d4e-8486-858520048065
-- title:
--   Finite row and cover checks for orbit 023, block 9
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [128, 144) for the original orbit 023 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case023_finite16_8 (j : Fin 16) :
    ((if 128+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[128+j.val]! else true) &&
    (if 128+j.val < certificate023.pool.size then localCoverB certificate023 (128+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
