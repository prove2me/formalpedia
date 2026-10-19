-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Cap_capP_three_sphere
-- name    : OAI.GaussianPropeller.Cap.capP_three_sphere
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T06:46:12.335631+00:00
-- url     : https://prove2.me/theorems/1990989a-457d-48a7-a7cc-636d4413e686
-- title:
--   Cap probability in dimension three through a spherical integral
-- statement:
--   Let $Y$ be a standard Gaussian vector in $\mathbb R^n$, $p$ the standard normal tail probability and $\varphi$ the standard normal density. Let $P_n(a)=\mathbb E\,p(a|Y|)$ and $M_n(a)=\mathbb E\,\varphi(a|Y|)$; in $\mathbb R^{n+1}$, $P_n(a)$ is the Gaussian measure of the cone $\{x:a|(x_1,\dots,x_n)|<x_0\}$ and $M_n(a)$ is its first moment $\int x_0$. Then for $-1<b<1$,
--   $$
--   P_3\Bigl(\frac b{\sqrt{1-b^2}}\Bigr)=\frac2\pi\int_b^1\sqrt{1-u^2}\,du .
--   $$
--
--   In $\mathbb R^4$ the Gaussian measure of a circular cone is a normalized area of a disc segment.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CapBounds.lean#L269-L286

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
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds

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
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open OneCell ProbabilityBounds Polar
open scoped Topology

theorem OAI.GaussianPropeller.Cap.capP_three_sphere {b:ℝ} (hb:b∈Ioo (-1:ℝ) 1) :
    capP 3 (b/Real.sqrt (1-b^2)) = 2/Real.pi*sphereTail b := by sorry
