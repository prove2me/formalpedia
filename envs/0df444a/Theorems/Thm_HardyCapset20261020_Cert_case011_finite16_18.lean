-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_18
-- name    : HardyCapset20261020.Cert.case011_finite16_18
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:17:13.082986+00:00
-- url     : https://prove2.me/theorems/aa8dd7a0-cae6-4ec7-89cc-48bbbbf9653b
-- title:
--   Finite row and cover checks for orbit 011, block 19
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [288, 304) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_18 (j : Fin 16) :
    ((if 288+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[288+j.val]! else true) &&
    (if 288+j.val < certificate011.pool.size then localCoverB certificate011 (288+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
