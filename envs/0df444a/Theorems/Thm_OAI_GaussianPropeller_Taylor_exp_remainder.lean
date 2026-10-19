-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Taylor_exp_remainder
-- name    : OAI.GaussianPropeller.Taylor.exp_remainder
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:22:08.360906+00:00
-- url     : https://prove2.me/theorems/0d0ffde8-075b-48e5-b72c-8cfa43bf9310
-- title:
--   Lagrange remainder for the exponential
-- statement:
--   Let $E_n(x)=\sum_{k=0}^n\frac{(-x)^k}{k!}$. For $x>0$ and every $n$ there is $c$ with
--   $$
--   e^{-x}-E_n(x)=(-1)^{n+1}\,e^{-c}\,\frac{x^{n+1}}{(n+1)!}.
--   $$
--
--   In particular the partial sums alternate around $e^{-x}$: the even ones lie above and the odd ones below.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Taylor.lean#L41-L57

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

theorem OAI.GaussianPropeller.Taylor.exp_remainder {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∃ c : ℝ, Real.exp (-x)-E n x =
      (-1:ℝ)^(n+1)*Real.exp (-c)*x^(n+1)/(Nat.factorial (n+1)) := by sorry
