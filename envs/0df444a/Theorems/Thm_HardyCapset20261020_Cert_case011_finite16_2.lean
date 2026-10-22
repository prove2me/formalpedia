-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_2
-- name    : HardyCapset20261020.Cert.case011_finite16_2
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:14:33.984987+00:00
-- url     : https://prove2.me/theorems/47a97efc-9f36-477a-a0d6-12a4852f1aa2
-- title:
--   Finite row and cover checks for orbit 011, block 3
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [32, 48) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_2 (j : Fin 16) :
    ((if 32+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[32+j.val]! else true) &&
    (if 32+j.val < certificate011.pool.size then localCoverB certificate011 (32+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
