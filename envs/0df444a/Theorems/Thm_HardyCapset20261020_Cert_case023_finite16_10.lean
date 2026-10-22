-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case023_finite16_10
-- name    : HardyCapset20261020.Cert.case023_finite16_10
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:24:29.80924+00:00
-- url     : https://prove2.me/theorems/e51040a6-16b7-4eca-af75-877046738c14
-- title:
--   Finite row and cover checks for orbit 023, block 11
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [160, 176) for the original orbit 023 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case023_finite16_10 (j : Fin 16) :
    ((if 160+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[160+j.val]! else true) &&
    (if 160+j.val < certificate023.pool.size then localCoverB certificate023 (160+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
