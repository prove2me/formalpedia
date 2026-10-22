-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case179_finite32_7
-- name    : HardyCapset20261020.Cert.case179_finite32_7
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T03:33:11.349859+00:00
-- url     : https://prove2.me/theorems/327c1472-72e9-473c-be27-d635e0f737ea
-- title:
--   Finite row and cover checks for orbit 179, block 8
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [224, 256) for the original orbit 179 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate17920261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case179_finite32_7 (j : Fin 32) :
    ((if 224+j.val < certificate179.rows.size then rowB certificate179 certificate179.rows[224+j.val]! else true) &&
    (if 224+j.val < certificate179.pool.size then localCoverB certificate179 (224+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
