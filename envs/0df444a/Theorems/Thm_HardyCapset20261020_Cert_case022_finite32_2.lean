-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case022_finite32_2
-- name    : HardyCapset20261020.Cert.case022_finite32_2
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:00:49.437264+00:00
-- url     : https://prove2.me/theorems/b2b2e1fb-fd6e-4e30-a41d-1f9ea5c50b09
-- title:
--   Finite row and cover checks for orbit 022, block 3
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [64, 96) for the original orbit 022 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02220261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case022_finite32_2 (j : Fin 32) :
    ((if 64+j.val < certificate022.rows.size then rowB certificate022 certificate022.rows[64+j.val]! else true) &&
    (if 64+j.val < certificate022.pool.size then localCoverB certificate022 (64+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
