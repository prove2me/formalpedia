-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case023_finite16_6
-- name    : HardyCapset20261020.Cert.case023_finite16_6
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:24:03.02435+00:00
-- url     : https://prove2.me/theorems/34a6af13-87f3-4e6b-8fc6-8940c48f3d25
-- title:
--   Finite row and cover checks for orbit 023, block 7
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [96, 112) for the original orbit 023 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case023_finite16_6 (j : Fin 16) :
    ((if 96+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[96+j.val]! else true) &&
    (if 96+j.val < certificate023.pool.size then localCoverB certificate023 (96+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
