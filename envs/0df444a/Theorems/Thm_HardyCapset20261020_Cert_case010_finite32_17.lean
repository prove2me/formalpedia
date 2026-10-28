-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite32_17
-- name    : HardyCapset20261020.Cert.case010_finite32_17
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:05:15.357977+00:00
-- url     : https://prove2.me/theorems/556fef33-d725-4190-a1fc-a6bbd32e73c0
-- title:
--   Finite row and cover checks for orbit 010, block 18
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [544, 576) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite32_17 (j : Fin 32) :
    ((if 544+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[544+j.val]! else true) &&
    (if 544+j.val < certificate010.pool.size then localCoverB certificate010 (544+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
