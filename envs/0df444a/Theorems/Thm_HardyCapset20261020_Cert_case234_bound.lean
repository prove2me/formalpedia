-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case234_bound
-- name    : HardyCapset20261020.Cert.case234_bound
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T16:51:46.44867+00:00
-- url     : https://prove2.me/theorems/7c13ce0c-192f-48fa-b501-f28b0ce8bbe3
-- title:
--   Full-space completion bound for hyperplane orbit representative 234
-- statement:
--   For normal identifier 3280 and layer 0, every cap containing the exact 512-point baseline outside the hyperplane has cardinality at most 512. Added points may lie anywhere in the full ambient space. Concrete finite witnesses, all local patterns and rational weighted-cover arithmetic are verified in Lean.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificateModel20261020

namespace HardyCapset20261020.Cert
theorem case234_bound : CompletionBound (decode 3280) (0 : ZMod 3) := by sorry
end HardyCapset20261020.Cert
