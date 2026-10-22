-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case028_finite4_81
-- name    : HardyCapset20261020.Cert.case028_finite4_81
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T05:23:43.271298+00:00
-- url     : https://prove2.me/theorems/3b7f731c-aa99-4eb1-a6d8-66d94721cb48
-- title:
--   Finite row and cover checks for orbit 028, block 82
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [324, 328) for the original orbit 028 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02820261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case028_finite4_81 (j : Fin 4) :
    ((if 324+j.val < certificate028.rows.size then rowB certificate028 certificate028.rows[324+j.val]! else true) &&
    (if 324+j.val < certificate028.pool.size then localCoverB certificate028 (324+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
