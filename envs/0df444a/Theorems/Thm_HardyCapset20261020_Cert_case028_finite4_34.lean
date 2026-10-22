-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_34
-- name    : HardyCapset20261020.Cert.case028_finite4_34
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:15:37.680191+00:00
-- url     : https://prove2.me/theorems/f212c80e-4cd3-4eb5-9597-51af5eec057e
-- title:
--   Finite row and cover checks for orbit 028, block 35
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [136, 140) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_34 (j : Fin 4) :
    ((if 136+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[136+j.val]! else true) &&
    (if 136+j.val < certificate028.pool.size then localCoverB certificate028 (136+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
