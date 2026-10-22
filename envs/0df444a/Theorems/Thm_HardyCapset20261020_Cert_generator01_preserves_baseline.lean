-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_generator01_preserves_baseline
-- name    : HardyCapset20261020.Cert.generator01_preserves_baseline
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T16:00:58.994542+00:00
-- url     : https://prove2.me/theorems/f1c17bd5-5826-4f91-bda5-6f7f43392488
-- title:
--   Baseline invariance under signed-permutation generator 1
-- statement:
--   The explicitly defined signed coordinate permutation generator 1 maps the exact 512-point baseline onto itself. The assertion is equality of the entire image set with the baseline, with no restriction to a sample of points.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetSymmetryData20261020
import Mathlib.Data.List.Sort
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000

namespace HardyCapset20261020.Cert
theorem generator01_preserves_baseline : PreservesBaseline generator01 := by sorry
end HardyCapset20261020.Cert
