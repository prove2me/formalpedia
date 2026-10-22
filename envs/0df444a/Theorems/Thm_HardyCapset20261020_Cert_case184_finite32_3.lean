-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case184_finite32_3
-- name    : HardyCapset20261020.Cert.case184_finite32_3
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:46:34.597738+00:00
-- url     : https://prove2.me/theorems/5e7f40a3-c2f6-49a4-af1d-e726d6d8efe5
-- title:
--   Finite row and cover checks for orbit 184, block 4
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [96, 128) for the original orbit 184 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate18420261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case184_finite32_3 (j : Fin 32) :
    ((if 96+j.val < certificate184.rows.size then rowB certificate184 certificate184.rows[96+j.val]! else true) &&
    (if 96+j.val < certificate184.pool.size then localCoverB certificate184 (96+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
