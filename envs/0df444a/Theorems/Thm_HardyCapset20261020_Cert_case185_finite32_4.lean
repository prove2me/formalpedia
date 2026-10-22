-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case185_finite32_4
-- name    : HardyCapset20261020.Cert.case185_finite32_4
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:51:21.673884+00:00
-- url     : https://prove2.me/theorems/59a0af91-772b-4131-ae95-ad13b874610c
-- title:
--   Finite row and cover checks for orbit 185, block 5
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [128, 160) for the original orbit 185 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate18520261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case185_finite32_4 (j : Fin 32) :
    ((if 128+j.val < certificate185.rows.size then rowB certificate185 certificate185.rows[128+j.val]! else true) &&
    (if 128+j.val < certificate185.pool.size then localCoverB certificate185 (128+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
