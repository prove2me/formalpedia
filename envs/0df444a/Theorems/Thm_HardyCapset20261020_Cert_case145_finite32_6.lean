-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case145_finite32_6
-- name    : HardyCapset20261020.Cert.case145_finite32_6
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:56:50.92829+00:00
-- url     : https://prove2.me/theorems/393c3bad-5eb0-4349-a6ad-aa2e6e7d62c5
-- title:
--   Finite row and cover checks for orbit 145, block 7
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [192, 224) for the original orbit 145 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate14520261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case145_finite32_6 (j : Fin 32) :
    ((if 192+j.val < certificate145.rows.size then rowB certificate145 certificate145.rows[192+j.val]! else true) &&
    (if 192+j.val < certificate145.pool.size then localCoverB certificate145 (192+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
