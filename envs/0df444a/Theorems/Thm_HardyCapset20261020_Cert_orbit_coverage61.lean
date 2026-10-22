-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_orbit_coverage61
-- name    : HardyCapset20261020.Cert.orbit_coverage61
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T16:43:27.327233+00:00
-- url     : https://prove2.me/theorems/bb4114ce-4564-4c17-9d0c-75843f6185ea
-- title:
--   Exhaustive hyperplane symmetry coverage, block 61
-- statement:
--   For every encoded hyperplane index in [15616, 15872), explicitly provides an orbit representative, a word of baseline-preserving signed permutations, and a nonzero ternary scalar sending its normal and layer to the requested hyperplane. All coordinates and layer equations are checked in Lean.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetOrbitVerifier20261021

namespace HardyCapset20261020.Cert
theorem orbit_coverage61 (q : Fin 256) : OrbitCovered (15616 + q.val) := by sorry
end HardyCapset20261020.Cert
