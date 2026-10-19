-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_ProbabilityBounds_linear_quadratic_of_loss
-- name    : OAI.GaussianPropeller.ProbabilityBounds.linear_quadratic_of_loss
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:26:18.32916+00:00
-- url     : https://prove2.me/theorems/b950af03-69d5-493f-be4a-f208974aaf5e
-- title:
--   A large loss forces a linear-quadratic tail probability
-- statement:
--   Let $T(x)=\int_x^\infty e^{-t^2/2}\,dt$, let $p(x)=T(x)/\sqrt{2\pi}$ be the standard normal tail probability, let $\lambda(x)=e^{-x^2/2}/T(x)$ be the inverse Mills ratio and $G(x)=\lambda(x)(\lambda(x)-x)$. Let $L=p^2G$. If $0<r\le\frac23$, $x\ge0$ and
--   $$
--   \frac{9}{8\pi}\cdot\frac{r^2}{1+\sqrt{1-r^2}}\le L(x),
--   $$
--   then $0.415\,r+0.15\,r^2<p(x)$.
--
--   In a configuration, applied with $r$ the normalized centroid length, this is the linear lower bound on each cell's mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/ProbabilityBounds.lean#L406-L431

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
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.ProbabilityBounds
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
open OneCell Mills Taylor

theorem OAI.GaussianPropeller.ProbabilityBounds.linear_quadratic_of_loss {r x : ℝ} (hr : 0 < r) (hrcap : r ≤ 2/3) (hx : 0 ≤ x)
    (hc : (9/(8*Real.pi))*r^2/(1+Real.sqrt (1-r^2)) ≤ loss x) :
    0.415*r+0.15*r^2 < p x := by sorry
