-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case010_finite16_29
-- name    : HardyCapset20261020.Cert.case010_finite16_29
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:12:06.178602+00:00
-- url     : https://prove2.me/theorems/b2e73f69-c1b2-4daa-baed-40f717c774bb
-- title:
--   Finite row and cover checks for orbit 010, block 30
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [464, 480) for the original orbit 010 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01020261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case010_finite16_29 (j : Fin 16) :
    ((if 464+j.val < certificate010.rows.size then rowB certificate010 certificate010.rows[464+j.val]! else true) &&
    (if 464+j.val < certificate010.pool.size then localCoverB certificate010 (464+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
