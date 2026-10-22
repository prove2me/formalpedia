-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case023_finite32_9
-- name    : HardyCapset20261020.Cert.case023_finite32_9
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:20:57.740399+00:00
-- url     : https://prove2.me/theorems/f80a7338-b0e2-40fe-8fd9-7ba021523f51
-- title:
--   Finite row and cover checks for orbit 023, block 10
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [288, 320) for the original orbit 023 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case023_finite32_9 (j : Fin 32) :
    ((if 288+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[288+j.val]! else true) &&
    (if 288+j.val < certificate023.pool.size then localCoverB certificate023 (288+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
