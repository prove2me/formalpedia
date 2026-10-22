-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_26
-- name    : HardyCapset20261020.Cert.case011_finite16_26
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:18:34.012652+00:00
-- url     : https://prove2.me/theorems/27f48736-b498-4bbb-98c1-1a8f6abf1666
-- title:
--   Finite row and cover checks for orbit 011, block 27
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [416, 432) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_26 (j : Fin 16) :
    ((if 416+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[416+j.val]! else true) &&
    (if 416+j.val < certificate011.pool.size then localCoverB certificate011 (416+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
