-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case184_finite32_0
-- name    : HardyCapset20261020.Cert.case184_finite32_0
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:42:50.663375+00:00
-- url     : https://prove2.me/theorems/e5d0fd6f-7135-451b-9796-076a27175f9d
-- title:
--   Finite row and cover checks for orbit 184, block 1
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [0, 32) for the original orbit 184 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate18420261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case184_finite32_0 (j : Fin 32) :
    ((if 0+j.val < certificate184.rows.size then rowB certificate184 certificate184.rows[0+j.val]! else true) &&
    (if 0+j.val < certificate184.pool.size then localCoverB certificate184 (0+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
