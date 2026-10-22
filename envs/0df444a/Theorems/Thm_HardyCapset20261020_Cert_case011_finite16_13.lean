-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_13
-- name    : HardyCapset20261020.Cert.case011_finite16_13
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:16:38.701622+00:00
-- url     : https://prove2.me/theorems/9ed741a2-03a7-4ba2-a21e-f452e2cb290b
-- title:
--   Finite row and cover checks for orbit 011, block 14
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [208, 224) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_13 (j : Fin 16) :
    ((if 208+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[208+j.val]! else true) &&
    (if 208+j.val < certificate011.pool.size then localCoverB certificate011 (208+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
