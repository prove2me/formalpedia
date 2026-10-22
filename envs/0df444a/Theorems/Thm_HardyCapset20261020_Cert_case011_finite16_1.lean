-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_1
-- name    : HardyCapset20261020.Cert.case011_finite16_1
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:14:25.60735+00:00
-- url     : https://prove2.me/theorems/5e5bf013-7f18-46e5-8fb6-b7614e26caef
-- title:
--   Finite row and cover checks for orbit 011, block 2
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [16, 32) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_1 (j : Fin 16) :
    ((if 16+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[16+j.val]! else true) &&
    (if 16+j.val < certificate011.pool.size then localCoverB certificate011 (16+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
