-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Mills_inverse_mills_ratio_deriv_le_one
-- name    : OAI.GaussianPropeller.Mills.inverse_mills_ratio_deriv_le_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:17:45.94337+00:00
-- url     : https://prove2.me/theorems/f9f6fefb-9a5d-401d-95cb-0e8c2e13f4b9
-- title:
--   The derivative λ(λ − x) of the Gaussian inverse Mills ratio λ(x) is at most 1
-- statement:
--   For a real number $x$ let
--   $$\lambda(x) = \frac{e^{-x^2/2}}{\int_x^\infty e^{-t^2/2}\,dt},$$
--   the inverse Mills ratio of the standard normal distribution, where the integral is the Lebesgue integral over the open half-line $(x, \infty)$ (`∫ t in Set.Ioi x, Real.exp (-t^2/2)`). Then for every real $x$,
--   $$\lambda(x)\,\bigl(\lambda(x) - x\bigr) \;\le\; 1.$$
--   There is no restriction on the sign of $x$. Here $\lambda(x)(\lambda(x) - x)$ is the derivative $\lambda'(x)$ (OpenAI's lemma `hasDerivAt_lambda`), so the statement is the bound $\lambda' \le 1$.
--
--   Lean: `OAI.GaussianPropeller.Mills.inverse_mills_ratio_deriv_le_one`. It uses only Mathlib. OpenAI's lemma `G_le_one` states `G x ≤ 1` with `G x = lambda x * (lambda x - x)`, `lambda x = density x / tail x`, `density x = Real.exp (-x^2/2)` and `tail x = ∫ t in Ioi x, density t`; this statement unfolds those definitions.
-- source:
--   Classical bound on Mills' ratio; cf. M. R. Sampford, Some inequalities on Mill's ratio and related functions, Annals of Mathematical Statistics 24 (1953), 130–132. Proof: OpenAI, The Gaussian propeller bound in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 096, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianPropeller/Mills.lean (OpenAI's lemma OAI.GaussianPropeller.Mills.G_le_one, restated with its definitions unfolded)

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

theorem inverse_mills_ratio_deriv_le_one (x : ℝ) :
    (Real.exp (-x^2/2) / ∫ t in Set.Ioi x, Real.exp (-t^2/2)) *
      (Real.exp (-x^2/2) / (∫ t in Set.Ioi x, Real.exp (-t^2/2)) - x) ≤ 1 := by
  sorry

end GaussianPropeller.Mills

end OAI
end
