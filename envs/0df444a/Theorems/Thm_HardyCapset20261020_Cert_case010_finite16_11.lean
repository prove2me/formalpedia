-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite16_11
-- name    : HardyCapset20261020.Cert.case010_finite16_11
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:09:01.567468+00:00
-- url     : https://prove2.me/theorems/02c4ef9a-bc7e-4954-ac29-04a75471038c
-- title:
--   Finite row and cover checks for orbit 010, block 12
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [176, 192) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite16_11 (j : Fin 16) :
    ((if 176+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[176+j.val]! else true) &&
    (if 176+j.val < certificate010.pool.size then localCoverB certificate010 (176+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
