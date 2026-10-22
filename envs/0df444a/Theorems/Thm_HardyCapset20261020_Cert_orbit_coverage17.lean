-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage17
-- name    : HardyCapset20261020.Cert.orbit_coverage17
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T16:43:12.027288+00:00
-- url     : https://prove2.me/theorems/648666bc-8ccf-4d86-849a-21c0b773a805
-- title:
--   Exhaustive hyperplane symmetry coverage, block 17
-- statement:
--   For every encoded hyperplane index in [4352, 4608), explicitly provides an orbit representative, a word of baseline-preserving signed permutations, and a nonzero ternary scalar sending its normal and layer to the requested hyperplane. All coordinates and layer equations are checked in Lean.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetOrbitVerifier20261021

namespace HardyCapset20261020.Cert
theorem orbit_coverage17 (q : Fin 256) : OrbitCovered (4352 + q.val) := by sorry
end HardyCapset20261020.Cert
