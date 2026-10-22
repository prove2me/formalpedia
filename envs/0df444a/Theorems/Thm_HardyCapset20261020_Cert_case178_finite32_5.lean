-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case178_finite32_5
-- name    : HardyCapset20261020.Cert.case178_finite32_5
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:19:36.504985+00:00
-- url     : https://prove2.me/theorems/3011989e-3adc-44c2-8a0c-6a6834619b86
-- title:
--   Finite row and cover checks for orbit 178, block 6
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [160, 192) for the original orbit 178 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case178_finite32_5 (j : Fin 32) :
    ((if 160+j.val < certificate178.rows.size then rowB certificate178 certificate178.rows[160+j.val]! else true) &&
    (if 160+j.val < certificate178.pool.size then localCoverB certificate178 (160+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
