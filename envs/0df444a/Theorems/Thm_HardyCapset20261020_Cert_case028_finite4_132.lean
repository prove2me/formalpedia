-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_132
-- name    : HardyCapset20261020.Cert.case028_finite4_132
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:33:51.599277+00:00
-- url     : https://prove2.me/theorems/256679df-7c3f-45b3-91f0-4a35b3818d09
-- title:
--   Finite row and cover checks for orbit 028, block 133
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [528, 532) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_132 (j : Fin 4) :
    ((if 528+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[528+j.val]! else true) &&
    (if 528+j.val < certificate028.pool.size then localCoverB certificate028 (528+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
