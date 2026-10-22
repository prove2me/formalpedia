-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite16_5
-- name    : HardyCapset20261020.Cert.case010_finite16_5
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:08:01.177603+00:00
-- url     : https://prove2.me/theorems/6df01b25-9c1c-4848-9413-231c3068e056
-- title:
--   Finite row and cover checks for orbit 010, block 6
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [80, 96) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite16_5 (j : Fin 16) :
    ((if 80+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[80+j.val]! else true) &&
    (if 80+j.val < certificate010.pool.size then localCoverB certificate010 (80+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
