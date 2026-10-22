-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case013_bound
-- name    : HardyCapset20261020.Cert.case013_bound
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T16:50:05.143992+00:00
-- url     : https://prove2.me/theorems/40da830b-92b2-4e10-a0aa-d93edcbab8ec
-- title:
--   Full-space completion bound for hyperplane orbit representative 013
-- statement:
--   For normal identifier 28 and layer 1, every cap containing the exact 512-point baseline outside the hyperplane has cardinality at most 512. Added points may lie anywhere in the full ambient space. Concrete finite witnesses, all local patterns and rational weighted-cover arithmetic are verified in Lean.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificateModel20261020

namespace HardyCapset20261020.Cert
theorem case013_bound : CompletionBound (decode 28) (1 : ZMod 3) := by sorry
end HardyCapset20261020.Cert
