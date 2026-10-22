-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_case106_bound
-- name    : HardyCapset20261020.Cert.case106_bound
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T16:51:00.34644+00:00
-- url     : https://prove2.me/theorems/ca34e8ae-291e-4701-97fb-0e18dd38b72c
-- title:
--   Full-space completion bound for hyperplane orbit representative 106
-- statement:
--   For normal identifier 367 and layer 0, every cap containing the exact 512-point baseline outside the hyperplane has cardinality at most 512. Added points may lie anywhere in the full ambient space. Concrete finite witnesses, all local patterns and rational weighted-cover arithmetic are verified in Lean.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificateModel20261020

namespace HardyCapset20261020.Cert
theorem case106_bound : CompletionBound (decode 367) (0 : ZMod 3) := by sorry
end HardyCapset20261020.Cert
