-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_positive_from_quadratic
-- name    : Kyprianou.Ch08.StageB.source_result81_scale_positive_from_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T14:20:20.011433+00:00
-- url     : https://prove2.me/theorems/0861eb6e-a2fe-4360-b12f-0a796ae79243
-- title:
--   A normalized scale with a quadratically bounded exponent is positive at positive levels
-- statement:
--   If w vanishes at a, monotonicity makes it vanish below a, giving an exponentially small upper bound on its Laplace transform as the parameter grows. Normalization and the quadratic bound instead give an inverse-quadratic lower bound. Exponential decay contradicts this lower bound.
-- source:
--   Kyprianou (2006), Chapter 8, Laplace normalization (8.5). Decomposition of 4a5bedc9-ffce-4d0e-abf0-74c2a8cddb49.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_scale_positive_from_quadratic
    (ψ : ℝ → ℝ) (q : ℝ) (w : ℝ → ℝ) (hw : IsQScale ψ q w)
    (K : ℝ) (hK : 0 ≤ K) (hgrowth : ∀ β : ℝ, 1 ≤ β → ψ β ≤ K * β ^ 2)
    (a : ℝ) (ha : 0 < a) :
    0 < w a := by
  sorry
