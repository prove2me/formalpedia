-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_ProbabilityBounds_loss_antitone
-- name    : OAI.GaussianPropeller.ProbabilityBounds.loss_antitone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:24:41.509182+00:00
-- url     : https://prove2.me/theorems/402c1e4a-fa44-451f-ab04-60e29f35f277
-- title:
--   The loss function is decreasing
-- statement:
--   Let $T(x)=\int_x^\infty e^{-t^2/2}\,dt$, let $p(x)=T(x)/\sqrt{2\pi}$ be the standard normal tail probability, let $\lambda(x)=e^{-x^2/2}/T(x)$ be the inverse Mills ratio and $G(x)=\lambda(x)(\lambda(x)-x)$. Let $L(x)=p(x)^2\,G(x)$. Then $L$ is nonincreasing on $[0,\infty)$:
--   $$
--   0\le x\le y\ \Longrightarrow\ L(y)\le L(x).
--   $$
--
--   So a lower bound on the loss forces an upper bound on the threshold $x$, and hence a lower bound on the tail probability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/ProbabilityBounds.lean#L241-L255

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

theorem OAI.GaussianPropeller.ProbabilityBounds.loss_antitone : AntitoneOn loss (Ici 0) := by sorry
