-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_12
-- name    : HardyCapset20261020.Cert.case011_finite16_12
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:16:13.486592+00:00
-- url     : https://prove2.me/theorems/0df3eb05-c6ac-48e5-b719-d19aa189df83
-- title:
--   Finite row and cover checks for orbit 011, block 13
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [192, 208) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_12 (j : Fin 16) :
    ((if 192+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[192+j.val]! else true) &&
    (if 192+j.val < certificate011.pool.size then localCoverB certificate011 (192+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
