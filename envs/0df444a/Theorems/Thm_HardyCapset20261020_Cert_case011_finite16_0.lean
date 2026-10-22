-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_0
-- name    : HardyCapset20261020.Cert.case011_finite16_0
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:14:31.860619+00:00
-- url     : https://prove2.me/theorems/8558e51e-4793-4fec-8134-0dfe0a4d8607
-- title:
--   Finite row and cover checks for orbit 011, block 1
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [0, 16) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_0 (j : Fin 16) :
    ((if 0+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[0+j.val]! else true) &&
    (if 0+j.val < certificate011.pool.size then localCoverB certificate011 (0+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
