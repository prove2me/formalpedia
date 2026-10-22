-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case063_finite32_5
-- name    : HardyCapset20261020.Cert.case063_finite32_5
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:41:49.027035+00:00
-- url     : https://prove2.me/theorems/3a2695a6-ba5a-4d85-86b2-8f17aaaf69a6
-- title:
--   Finite row and cover checks for orbit 063, block 6
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [160, 192) for the original orbit 063 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate06320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case063_finite32_5 (j : Fin 32) :
    ((if 160+j.val < certificate063.rows.size then rowB certificate063 certificate063.rows[160+j.val]! else true) &&
    (if 160+j.val < certificate063.pool.size then localCoverB certificate063 (160+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
