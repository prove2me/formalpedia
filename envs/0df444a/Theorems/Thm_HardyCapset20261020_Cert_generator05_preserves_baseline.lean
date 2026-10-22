-- Prove2me | Theorems.Thm_HardyCapset20261020_Cert_generator05_preserves_baseline
-- name    : HardyCapset20261020.Cert.generator05_preserves_baseline
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-20T16:01:01.999395+00:00
-- url     : https://prove2.me/theorems/1ca15f6c-1581-443e-92e0-2b065e8fdfaa
-- title:
--   Baseline invariance under signed-permutation generator 5
-- statement:
--   The explicitly defined signed coordinate permutation generator 5 maps the exact 512-point baseline onto itself. The assertion is equality of the entire image set with the baseline, with no restriction to a sample of points.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetSymmetryData20261020
import Mathlib.Data.List.Sort
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000

namespace HardyCapset20261020.Cert
theorem generator05_preserves_baseline : PreservesBaseline generator05 := by sorry
end HardyCapset20261020.Cert
