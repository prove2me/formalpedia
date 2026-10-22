-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_15
-- name    : HardyCapset20261020.Cert.case011_finite16_15
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:16:44.525793+00:00
-- url     : https://prove2.me/theorems/3f53e0b9-f937-46b9-95e8-90eb6cff1d64
-- title:
--   Finite row and cover checks for orbit 011, block 16
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [240, 256) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_15 (j : Fin 16) :
    ((if 240+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[240+j.val]! else true) &&
    (if 240+j.val < certificate011.pool.size then localCoverB certificate011 (240+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
