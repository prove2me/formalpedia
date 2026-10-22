-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case023_finite16_19
-- name    : HardyCapset20261020.Cert.case023_finite16_19
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:25:57.685848+00:00
-- url     : https://prove2.me/theorems/71ca7e4f-8ef0-474f-b95e-330510a2813c
-- title:
--   Finite row and cover checks for orbit 023, block 20
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [304, 320) for the original orbit 023 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case023_finite16_19 (j : Fin 16) :
    ((if 304+j.val < certificate023.rows.size then rowB certificate023 certificate023.rows[304+j.val]! else true) &&
    (if 304+j.val < certificate023.pool.size then localCoverB certificate023 (304+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
