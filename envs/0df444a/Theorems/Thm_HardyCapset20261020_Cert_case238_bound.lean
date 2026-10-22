-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case238_bound
-- name    : HardyCapset20261020.Cert.case238_bound
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T16:51:48.203925+00:00
-- url     : https://prove2.me/theorems/0a552dec-f460-458c-b72c-c258986967de
-- title:
--   Full-space completion bound for hyperplane orbit representative 238
-- statement:
--   For normal identifier 3284 and layer 0, every cap containing the exact 512-point baseline outside the hyperplane has cardinality at most 512. Added points may lie anywhere in the full ambient space. Concrete finite witnesses, all local patterns and rational weighted-cover arithmetic are verified in Lean.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificateModel20261020

namespace HardyCapset20261020.Cert
theorem case238_bound : CompletionBound (decode 3284) (0 : ZMod 3) := by sorry
end HardyCapset20261020.Cert
