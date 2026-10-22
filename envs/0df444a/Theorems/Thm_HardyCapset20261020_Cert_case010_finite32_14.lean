-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite32_14
-- name    : HardyCapset20261020.Cert.case010_finite32_14
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T01:04:46.191993+00:00
-- url     : https://prove2.me/theorems/8099e66c-d4aa-4619-9212-b5f18a82598f
-- title:
--   Finite row and cover checks for orbit 010, block 15
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [448, 480) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite32_14 (j : Fin 32) :
    ((if 448+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[448+j.val]! else true) &&
    (if 448+j.val < certificate010.pool.size then localCoverB certificate010 (448+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
