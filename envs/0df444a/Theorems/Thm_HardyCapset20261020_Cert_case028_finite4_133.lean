-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_133
-- name    : HardyCapset20261020.Cert.case028_finite4_133
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:34:04.399709+00:00
-- url     : https://prove2.me/theorems/c2a95cff-e057-4aa8-8150-3b2a82eee439
-- title:
--   Finite row and cover checks for orbit 028, block 134
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [532, 536) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_133 (j : Fin 4) :
    ((if 532+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[532+j.val]! else true) &&
    (if 532+j.val < certificate028.pool.size then localCoverB certificate028 (532+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
