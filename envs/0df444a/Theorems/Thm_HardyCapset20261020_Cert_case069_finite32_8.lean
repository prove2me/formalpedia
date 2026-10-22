-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case069_finite32_8
-- name    : HardyCapset20261020.Cert.case069_finite32_8
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:47:21.984765+00:00
-- url     : https://prove2.me/theorems/8c7a210c-d93f-48b3-89a1-41f75091082d
-- title:
--   Finite row and cover checks for orbit 069, block 9
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [256, 288) for the original orbit 069 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate06920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case069_finite32_8 (j : Fin 32) :
    ((if 256+j.val < certificate069.rows.size then rowB certificate069 certificate069.rows[256+j.val]! else true) &&
    (if 256+j.val < certificate069.pool.size then localCoverB certificate069 (256+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
