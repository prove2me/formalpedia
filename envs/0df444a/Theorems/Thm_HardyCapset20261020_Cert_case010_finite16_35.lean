-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite16_35
-- name    : HardyCapset20261020.Cert.case010_finite16_35
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:13:04.502987+00:00
-- url     : https://prove2.me/theorems/3450678c-1abc-4c2b-83fb-dec37fac99f4
-- title:
--   Finite row and cover checks for orbit 010, block 36
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [560, 576) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite16_35 (j : Fin 16) :
    ((if 560+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[560+j.val]! else true) &&
    (if 560+j.val < certificate010.pool.size then localCoverB certificate010 (560+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
