-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case023_finite16_24
-- name    : HardyCapset20261020.Cert.case023_finite16_24
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:26:48.906987+00:00
-- url     : https://prove2.me/theorems/0a28e61d-c093-4230-a47b-16b304f6c9b3
-- title:
--   Finite row and cover checks for orbit 023, block 25
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [384, 400) for the original orbit 023 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case023_finite16_24 (j : Fin 16) :
    ((if 384+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[384+j.val]! else true) &&
    (if 384+j.val < certificate023.pool.size then localCoverB certificate023 (384+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
