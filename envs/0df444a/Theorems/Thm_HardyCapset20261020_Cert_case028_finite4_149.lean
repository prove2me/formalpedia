-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_149
-- name    : HardyCapset20261020.Cert.case028_finite4_149
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:36:47.356809+00:00
-- url     : https://prove2.me/theorems/cbef72e7-06fa-43fb-8be0-c7d097b0fd87
-- title:
--   Finite row and cover checks for orbit 028, block 150
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [596, 600) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_149 (j : Fin 4) :
    ((if 596+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[596+j.val]! else true) &&
    (if 596+j.val < certificate028.pool.size then localCoverB certificate028 (596+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
