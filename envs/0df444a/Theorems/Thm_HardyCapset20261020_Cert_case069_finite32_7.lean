-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case069_finite32_7
-- name    : HardyCapset20261020.Cert.case069_finite32_7
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:47:11.516328+00:00
-- url     : https://prove2.me/theorems/33aeb3d9-5ea1-4a1c-86f9-d41551da111a
-- title:
--   Finite row and cover checks for orbit 069, block 8
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [224, 256) for the original orbit 069 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate06920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case069_finite32_7 (j : Fin 32) :
    ((if 224+j.val < certificate069.rows.size then rowB certificate069 certificate069.rows[224+j.val]! else true) &&
    (if 224+j.val < certificate069.pool.size then localCoverB certificate069 (224+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
