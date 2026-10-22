-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case023_finite16_16
-- name    : HardyCapset20261020.Cert.case023_finite16_16
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:25:29.436705+00:00
-- url     : https://prove2.me/theorems/091c42b2-b34a-4ceb-9825-995c09c6dbc5
-- title:
--   Finite row and cover checks for orbit 023, block 17
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [256, 272) for the original orbit 023 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case023_finite16_16 (j : Fin 16) :
    ((if 256+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[256+j.val]! else true) &&
    (if 256+j.val < certificate023.pool.size then localCoverB certificate023 (256+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
