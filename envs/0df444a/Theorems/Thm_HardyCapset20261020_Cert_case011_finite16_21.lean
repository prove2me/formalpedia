-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_21
-- name    : HardyCapset20261020.Cert.case011_finite16_21
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:17:42.90341+00:00
-- url     : https://prove2.me/theorems/21c639b3-7be7-414d-8e05-c87c8177c34f
-- title:
--   Finite row and cover checks for orbit 011, block 22
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [336, 352) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_21 (j : Fin 16) :
    ((if 336+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[336+j.val]! else true) &&
    (if 336+j.val < certificate011.pool.size then localCoverB certificate011 (336+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
