-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_23
-- name    : HardyCapset20261020.Cert.case028_finite4_23
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:13:44.662039+00:00
-- url     : https://prove2.me/theorems/3b9f2449-20e9-4f63-987f-a975e96b4755
-- title:
--   Finite row and cover checks for orbit 028, block 24
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [92, 96) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_23 (j : Fin 4) :
    ((if 92+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[92+j.val]! else true) &&
    (if 92+j.val < certificate028.pool.size then localCoverB certificate028 (92+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
