-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_generator00_preserves_baseline
-- name    : HardyCapset20261020.Cert.generator00_preserves_baseline
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T16:01:01.18782+00:00
-- url     : https://prove2.me/theorems/56603a57-108c-44d9-ba4c-9bb5348bc66f
-- title:
--   Baseline invariance under signed-permutation generator 0
-- statement:
--   The explicitly defined signed coordinate permutation generator 0 maps the exact 512-point baseline onto itself. The assertion is equality of the entire image set with the baseline, with no restriction to a sample of points.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetSymmetryData20261020
import Mathlib.Data.List.Sort
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000

namespace HardyCapset20261020.Cert
theorem generator00_preserves_baseline : PreservesBaseline generator00 := by sorry
end HardyCapset20261020.Cert
