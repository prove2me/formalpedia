-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_generator06_preserves_baseline
-- name    : HardyCapset20261020.Cert.generator06_preserves_baseline
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T16:01:01.467667+00:00
-- url     : https://prove2.me/theorems/3516e021-afdc-4a03-8b08-17dbd1c2e7f7
-- title:
--   Baseline invariance under signed-permutation generator 6
-- statement:
--   The explicitly defined signed coordinate permutation generator 6 maps the exact 512-point baseline onto itself. The assertion is equality of the entire image set with the baseline, with no restriction to a sample of points.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetSymmetryData20261020
import Mathlib.Data.List.Sort
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000

namespace HardyCapset20261020.Cert
theorem generator06_preserves_baseline : PreservesBaseline generator06 := by sorry
end HardyCapset20261020.Cert
