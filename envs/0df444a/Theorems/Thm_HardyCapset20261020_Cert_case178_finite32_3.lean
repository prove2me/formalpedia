-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case178_finite32_3
-- name    : HardyCapset20261020.Cert.case178_finite32_3
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:19:09.537603+00:00
-- url     : https://prove2.me/theorems/a780bd93-4348-464c-98c6-f540b0dbc759
-- title:
--   Finite row and cover checks for orbit 178, block 4
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [96, 128) for the original orbit 178 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case178_finite32_3 (j : Fin 32) :
    ((if 96+j.val < certificate178.rows.size then rowB certificate178 certificate178.rows[96+j.val]! else true) &&
    (if 96+j.val < certificate178.pool.size then localCoverB certificate178 (96+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
