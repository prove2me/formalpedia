-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case059_finite32_6
-- name    : HardyCapset20261020.Cert.case059_finite32_6
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:38:04.726429+00:00
-- url     : https://prove2.me/theorems/a7141b54-3628-40b4-95e4-63d447b7acdc
-- title:
--   Finite row and cover checks for orbit 059, block 7
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [192, 224) for the original orbit 059 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate05920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case059_finite32_6 (j : Fin 32) :
    ((if 192+j.val < certificate059.rows.size then rowB certificate059 certificate059.rows[192+j.val]! else true) &&
    (if 192+j.val < certificate059.pool.size then localCoverB certificate059 (192+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
