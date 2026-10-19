-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Cap_hasDerivAt_capP
-- name    : OAI.GaussianPropeller.Cap.hasDerivAt_capP
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T06:40:48.50958+00:00
-- url     : https://prove2.me/theorems/db1d4ed7-e641-4252-8188-e0b9e2d6b8c5
-- title:
--   Derivative of the averaged cap probability
-- statement:
--   Let $Y$ be a standard Gaussian vector in $\mathbb R^n$, $p$ the standard normal tail probability and $\varphi$ the standard normal density. Let $P_n(a)=\mathbb E\,p(a|Y|)$ and $M_n(a)=\mathbb E\,\varphi(a|Y|)$; in $\mathbb R^{n+1}$, $P_n(a)$ is the Gaussian measure of the cone $\{x:a|(x_1,\dots,x_n)|<x_0\}$ and $M_n(a)$ is its first moment $\int x_0$. Then $P_n$ is differentiable, with
--   $$
--   P_n'(a)=-\frac1{\sqrt{2\pi}}\,\mathbb E\Bigl[|Y|\,e^{-a^2|Y|^2/2}\Bigr].
--   $$
--
--   Opening the cap angle loses mass at a rate given by a Gaussian moment.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CapIntegral.lean#L74-L98

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
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Cap
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open OneCell ProbabilityBounds Polar
open scoped Topology
variable {n : ℕ}

theorem OAI.GaussianPropeller.Cap.hasDerivAt_capP (a : ℝ) : HasDerivAt (capP n)
    (-gaussianConst * ∫ y : CE n, ‖y‖*density (a*‖y‖) ∂stdGaussian (CE n)) a := by sorry
