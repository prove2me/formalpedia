-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Taylor_integral_exp_bounds
-- name    : OAI.GaussianPropeller.Taylor.integral_exp_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:22:38.737023+00:00
-- url     : https://prove2.me/theorems/94c8c2db-1247-4dde-833c-e67f2feb6690
-- title:
--   Alternating bounds for the Gaussian integral
-- statement:
--   Let $J_n(x)=\sum_{k=0}^n\frac{(-1)^kx^{2k+1}}{2^kk!(2k+1)}$. For $x\ge0$ and every $n$,
--   $$
--   J_{2n+1}(x)\le\int_0^xe^{-t^2/2}\,dt\le J_{2n}(x).
--   $$
--
--   These rational bounds certify numerical values of the normal distribution function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Taylor.lean#L105-L119

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Taylor
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
open MeasureTheory Set Filter
open scoped Topology BigOperators

theorem OAI.GaussianPropeller.Taylor.integral_exp_bounds (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    J (2*n+1) x ≤ (∫ t in (0:ℝ)..x, Real.exp (-t^2/2)) ∧
      (∫ t in (0:ℝ)..x, Real.exp (-t^2/2)) ≤ J (2*n) x := by sorry
