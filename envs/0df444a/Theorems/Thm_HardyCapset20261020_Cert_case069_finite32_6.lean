-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case069_finite32_6
-- name    : HardyCapset20261020.Cert.case069_finite32_6
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:47:03.614884+00:00
-- url     : https://prove2.me/theorems/8fb85b8f-94c8-4336-9dea-a650093e8c41
-- title:
--   Finite row and cover checks for orbit 069, block 7
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [192, 224) for the original orbit 069 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate06920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case069_finite32_6 (j : Fin 32) :
    ((if 192+j.val < certificate069.rows.size then rowB certificate069 certificate069.rows[192+j.val]! else true) &&
    (if 192+j.val < certificate069.pool.size then localCoverB certificate069 (192+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
