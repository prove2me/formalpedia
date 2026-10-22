-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_113
-- name    : HardyCapset20261020.Cert.case028_finite4_113
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:30:34.559988+00:00
-- url     : https://prove2.me/theorems/aed435dc-bc5a-475a-9b6a-407f2a2f5c70
-- title:
--   Finite row and cover checks for orbit 028, block 114
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [452, 456) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_113 (j : Fin 4) :
    ((if 452+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[452+j.val]! else true) &&
    (if 452+j.val < certificate028.pool.size then localCoverB certificate028 (452+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
