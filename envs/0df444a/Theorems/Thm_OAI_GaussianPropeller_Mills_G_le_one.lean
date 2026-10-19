-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Mills_G_le_one
-- name    : OAI.GaussianPropeller.Mills.G_le_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:20:47.37397+00:00
-- url     : https://prove2.me/theorems/bf12ca1f-094f-43f5-9aea-5958927c3606
-- title:
--   The Mills-ratio product is at most one
-- statement:
--   Let $T(x)=\int_x^\infty e^{-t^2/2}\,dt$, let $p(x)=T(x)/\sqrt{2\pi}$ be the standard normal tail probability, let $\lambda(x)=e^{-x^2/2}/T(x)$ be the inverse Mills ratio and $G(x)=\lambda(x)(\lambda(x)-x)$. Then for every real $x$,
--   $$
--   G(x)=\lambda(x)\bigl(\lambda(x)-x\bigr)\le1 .
--   $$
--
--   Equivalently, the variance of a standard normal conditioned to exceed $x$ is nonnegative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Mills.lean#L160-L193

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

theorem OAI.GaussianPropeller.Mills.G_le_one (x : ℝ) : G x ≤ 1 := by sorry
