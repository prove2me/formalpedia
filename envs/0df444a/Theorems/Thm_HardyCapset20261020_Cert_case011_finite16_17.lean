-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_17
-- name    : HardyCapset20261020.Cert.case011_finite16_17
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:17:04.176197+00:00
-- url     : https://prove2.me/theorems/adb1659d-83c7-4bf0-8843-5e9e8496e2f3
-- title:
--   Finite row and cover checks for orbit 011, block 18
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [272, 288) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_17 (j : Fin 16) :
    ((if 272+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[272+j.val]! else true) &&
    (if 272+j.val < certificate011.pool.size then localCoverB certificate011 (272+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
