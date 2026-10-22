-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_148
-- name    : HardyCapset20261020.Cert.case028_finite4_148
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:36:36.90774+00:00
-- url     : https://prove2.me/theorems/e7d05e04-a8b2-4134-b8a2-039664ed63d4
-- title:
--   Finite row and cover checks for orbit 028, block 149
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [592, 596) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_148 (j : Fin 4) :
    ((if 592+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[592+j.val]! else true) &&
    (if 592+j.val < certificate028.pool.size then localCoverB certificate028 (592+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
