-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case069_finite32_13
-- name    : HardyCapset20261020.Cert.case069_finite32_13
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:48:13.407913+00:00
-- url     : https://prove2.me/theorems/8e546f81-ad95-454a-a193-57cad6d43eb4
-- title:
--   Finite row and cover checks for orbit 069, block 14
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [416, 448) for the original orbit 069 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate06920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case069_finite32_13 (j : Fin 32) :
    ((if 416+j.val < certificate069.rows.size then rowB certificate069 certificate069.rows[416+j.val]! else true) &&
    (if 416+j.val < certificate069.pool.size then localCoverB certificate069 (416+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
