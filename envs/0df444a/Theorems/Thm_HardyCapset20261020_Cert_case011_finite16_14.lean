-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case011_finite16_14
-- name    : HardyCapset20261020.Cert.case011_finite16_14
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-21T02:16:34.039906+00:00
-- url     : https://prove2.me/theorems/943fdb3b-992b-427e-829c-975804656be4
-- title:
--   Finite row and cover checks for orbit 011, block 15
-- statement:
--   Check every row capacity and every candidate weighted cover at indices [224, 240) for the original orbit 011 certificate. Out-of-range indices are padded with true; all original in-range checks are retained.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificate01120261021
import Definitions.Def_HardyCapsetBooleanVerifier20261020

namespace HardyCapset20261020.Cert
theorem case011_finite16_14 (j : Fin 16) :
    ((if 224+j.val < certificate011.rows.size then rowB certificate011 certificate011.rows[224+j.val]! else true) &&
    (if 224+j.val < certificate011.pool.size then localCoverB certificate011 (224+j.val) else true)) = true := by sorry
end HardyCapset20261020.Cert
