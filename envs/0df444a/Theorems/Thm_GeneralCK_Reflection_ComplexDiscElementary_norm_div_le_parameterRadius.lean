-- Prove2me | Theorems.Thm_GeneralCK_Reflection_ComplexDiscElementary_norm_div_le_parameterRadius
-- name    : GeneralCK.Reflection.ComplexDiscElementary.norm_div_le_parameterRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T21:03:17.093067+00:00
-- url     : https://prove2.me/theorems/9a94eaf6-3bdb-48c3-970a-bdbfd60d9a69
-- title:
--   A complex quotient stays within the contact parameter radius
-- statement:
--   For complex numbers $a,e$ satisfying $|a|\le21/50$ and $|e|\ge3/5$, $$|a/e|\le7/10.$$ The lower bound on the denominator ensures it is nonzero. This estimate puts the quotient parameter within the radius used by the complex-contact bounds.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexDiscElementary.lean#L136-L143

import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.Lipschitz
open Set

theorem GeneralCK.Reflection.ComplexDiscElementary.norm_div_le_parameterRadius
    {a e : ℂ} (ha : ‖a‖ ≤ (21 / 50 : ℝ))
    (he : (3 / 5 : ℝ) ≤ ‖e‖) :
    ‖a / e‖ ≤ (7 / 10 : ℝ) := by sorry
