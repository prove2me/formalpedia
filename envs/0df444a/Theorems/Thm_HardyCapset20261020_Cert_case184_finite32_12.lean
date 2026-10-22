-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case184_finite32_12
-- name    : HardyCapset20261020.Cert.case184_finite32_12
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:48:01.240795+00:00
-- url     : https://prove2.me/theorems/70b7144d-000a-42de-8058-a6c457bd291f
-- title:
--   Finite row and cover checks for orbit 184, block 13
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [384, 416) for the original orbit 184 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate18420261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case184_finite32_12 (j : Fin 32) :
    ((if 384+j.val < certificate184.rows.size then rowB certificate184 certificate184.rows[384+j.val]! else true) &&
    (if 384+j.val < certificate184.pool.size then localCoverB certificate184 (384+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
