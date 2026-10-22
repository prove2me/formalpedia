-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case184_finite32_6
-- name    : HardyCapset20261020.Cert.case184_finite32_6
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:47:07.393992+00:00
-- url     : https://prove2.me/theorems/1886bc1c-67c0-40b3-8055-9885b21a5767
-- title:
--   Finite row and cover checks for orbit 184, block 7
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [192, 224) for the original orbit 184 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate18420261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case184_finite32_6 (j : Fin 32) :
    ((if 192+j.val < certificate184.rows.size then rowB certificate184 certificate184.rows[192+j.val]! else true) &&
    (if 192+j.val < certificate184.pool.size then localCoverB certificate184 (192+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
