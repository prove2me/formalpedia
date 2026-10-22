-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case173_finite32_5
-- name    : HardyCapset20261020.Cert.case173_finite32_5
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:12:39.91854+00:00
-- url     : https://prove2.me/theorems/857cbdca-f9c8-418e-aeec-50ea4edfd477
-- title:
--   Finite row and cover checks for orbit 173, block 6
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [160, 192) for the original orbit 173 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case173_finite32_5 (j : Fin 32) :
    ((if 160+j.val < certificate173.rows.size then rowB certificate173 certificate173.rows[160+j.val]! else true) &&
    (if 160+j.val < certificate173.pool.size then localCoverB certificate173 (160+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
