-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Mills_gaussian_tail_le_sampford
-- name    : OAI.GaussianPropeller.Mills.gaussian_tail_le_sampford
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:17:44.774953+00:00
-- url     : https://prove2.me/theorems/308876c4-3473-4bf1-9541-21cd99df6e13
-- title:
--   Upper bound for the Gaussian tail (Mills' ratio): ∫ₓ^∞ e^(−t²/2) dt ≤ 4e^(−x²/2)/(3x + √(x²+8)) for x ≥ 0
-- statement:
--   For every real number $x \ge 0$,
--   $$\int_x^\infty e^{-t^2/2}\,dt \;\le\; \frac{e^{-x^2/2}}{\bigl(3x + \sqrt{x^2+8}\bigr)/4}.$$
--   The left side is the Lebesgue integral of $t \mapsto e^{-t^2/2}$ over the open half-line $(x, \infty)$ (`∫ t in Set.Ioi x, Real.exp (-t^2/2)`). On the right, `Real.sqrt` is the real square root. Equivalently, Mills' ratio $R(x) = \int_x^\infty e^{-t^2/2}\,dt \,/\, e^{-x^2/2}$ satisfies $R(x) \le 4/(3x + \sqrt{x^2+8})$ for $x \ge 0$.
--
--   Lean: `OAI.GaussianPropeller.Mills.gaussian_tail_le_sampford`. It uses only Mathlib. OpenAI's lemma `tail_le_barrier` states `tail x ≤ density x / barrier x` with `density x = Real.exp (-x^2/2)`, `tail x = ∫ t in Ioi x, density t` and `barrier x = (3*x + Real.sqrt (x^2+8))/4`; this statement unfolds those definitions.
-- source:
--   Classical bound on Mills' ratio; cf. M. R. Sampford, Some inequalities on Mill's ratio and related functions, Annals of Mathematical Statistics 24 (1953), 130–132. Proof: OpenAI, The Gaussian propeller bound in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 096, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianPropeller/Mills.lean (OpenAI's lemma OAI.GaussianPropeller.Mills.tail_le_barrier, restated with its definitions unfolded)

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.Mills

theorem gaussian_tail_le_sampford {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in Set.Ioi x, Real.exp (-t^2/2) ≤
      Real.exp (-x^2/2) / ((3*x + Real.sqrt (x^2+8))/4) := by
  sorry

end GaussianPropeller.Mills

end OAI
end
