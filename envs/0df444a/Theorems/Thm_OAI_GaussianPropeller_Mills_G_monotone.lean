-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Mills_G_monotone
-- name    : OAI.GaussianPropeller.Mills.G_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:19:14.620476+00:00
-- url     : https://prove2.me/theorems/32f3c216-7bb8-49b1-9022-41874bf468f4
-- title:
--   Monotonicity of the Mills-ratio product
-- statement:
--   Let $T(x)=\int_x^\infty e^{-t^2/2}\,dt$, let $p(x)=T(x)/\sqrt{2\pi}$ be the standard normal tail probability, let $\lambda(x)=e^{-x^2/2}/T(x)$ be the inverse Mills ratio and $G(x)=\lambda(x)(\lambda(x)-x)$. Then $G$ is nondecreasing on $[0,\infty)$:
--   $$
--   0\le x\le y\ \Longrightarrow\ G(x)\le G(y).
--   $$
--
--   Since $1-G(x)$ is the variance of a standard normal conditioned to exceed $x$, this says that variance decreases with the threshold.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Mills.lean#L135-L149

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

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Mills
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
open OneCell

theorem OAI.GaussianPropeller.Mills.G_monotone : MonotoneOn G (Ici 0) := by sorry
