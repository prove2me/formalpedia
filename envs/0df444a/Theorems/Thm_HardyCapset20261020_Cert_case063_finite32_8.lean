-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case063_finite32_8
-- name    : HardyCapset20261020.Cert.case063_finite32_8
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:42:20.956242+00:00
-- url     : https://prove2.me/theorems/b1af3677-e7e4-4caa-891f-7b718de37cda
-- title:
--   Finite row and cover checks for orbit 063, block 9
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [256, 288) for the original orbit 063 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate06320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case063_finite32_8 (j : Fin 32) :
    ((if 256+j.val < certificate063.rows.size then rowB certificate063 certificate063.rows[256+j.val]! else true) &&
    (if 256+j.val < certificate063.pool.size then localCoverB certificate063 (256+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
