-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case173_finite32_7
-- name    : HardyCapset20261020.Cert.case173_finite32_7
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:13:01.19913+00:00
-- url     : https://prove2.me/theorems/eb329664-ec41-4574-9459-1ad54cc25cd0
-- title:
--   Finite row and cover checks for orbit 173, block 8
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [224, 256) for the original orbit 173 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17320261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case173_finite32_7 (j : Fin 32) :
    ((if 224+j.val < certificate173.rows.size then rowB certificate173 certificate173.rows[224+j.val]! else true) &&
    (if 224+j.val < certificate173.pool.size then localCoverB certificate173 (224+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
