-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case022_finite32_17
-- name    : HardyCapset20261020.Cert.case022_finite32_17
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:03:17.459986+00:00
-- url     : https://prove2.me/theorems/a861eb80-d464-4639-a1d8-83e6b9e76f33
-- title:
--   Finite row and cover checks for orbit 022, block 18
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [544, 576) for the original orbit 022 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate02220261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case022_finite32_17 (j : Fin 32) :
    ((if 544+j.val < certificate022.rows.size then rowB certificate022 certificate022.rows[544+j.val]! else true) &&
    (if 544+j.val < certificate022.pool.size then localCoverB certificate022 (544+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
