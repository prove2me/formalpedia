-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case143_finite32_2
-- name    : HardyCapset20261020.Cert.case143_finite32_2
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:51:24.681539+00:00
-- url     : https://prove2.me/theorems/53b962a5-a87a-43f7-9126-d57e1b3df477
-- title:
--   Finite row and cover checks for orbit 143, block 3
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [64, 96) for the original orbit 143 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate14320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case143_finite32_2 (j : Fin 32) :
    ((if 64+j.val < certificate143.rows.size then rowB certificate143 certificate143.rows[64+j.val]! else true) &&
    (if 64+j.val < certificate143.pool.size then localCoverB certificate143 (64+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
