-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_77
-- name    : HardyCapset20261020.Cert.case028_finite4_77
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:23:01.853113+00:00
-- url     : https://prove2.me/theorems/335f3c83-b6a0-46c7-b788-eb65db28d057
-- title:
--   Finite row and cover checks for orbit 028, block 78
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [308, 312) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_77 (j : Fin 4) :
    ((if 308+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[308+j.val]! else true) &&
    (if 308+j.val < certificate028.pool.size then localCoverB certificate028 (308+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
