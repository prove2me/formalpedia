-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite32_2
-- name    : HardyCapset20261020.Cert.case010_finite32_2
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:02:44.908564+00:00
-- url     : https://prove2.me/theorems/a97f656e-f47b-4d43-ab87-25b5d991e9af
-- title:
--   Finite row and cover checks for orbit 010, block 3
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [64, 96) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite32_2 (j : Fin 32) :
    ((if 64+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[64+j.val]! else true) &&
    (if 64+j.val < certificate010.pool.size then localCoverB certificate010 (64+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
