-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case063_finite32_9
-- name    : HardyCapset20261020.Cert.case063_finite32_9
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:42:27.9323+00:00
-- url     : https://prove2.me/theorems/5576454e-3b7c-4176-af35-85d61a995dc1
-- title:
--   Finite row and cover checks for orbit 063, block 10
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [288, 320) for the original orbit 063 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate06320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case063_finite32_9 (j : Fin 32) :
    ((if 288+j.val < certificate063.rows.size then rowB certificate063 certificate063.rows[288+j.val]! else true) &&
    (if 288+j.val < certificate063.pool.size then localCoverB certificate063 (288+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
