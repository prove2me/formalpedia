-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Cap_moment_rearrange
-- name    : OAI.GaussianPropeller.Cap.moment_rearrange
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T06:43:42.409602+00:00
-- url     : https://prove2.me/theorems/0ad622e5-a0bc-4e68-a086-951a8848d652
-- title:
--   Rearrangement bound for the first coordinate moment of a cone
-- statement:
--   Let $Y$ be a standard Gaussian vector in $\mathbb R^n$, $p$ the standard normal tail probability and $\varphi$ the standard normal density. Let $P_n(a)=\mathbb E\,p(a|Y|)$ and $M_n(a)=\mathbb E\,\varphi(a|Y|)$; in $\mathbb R^{n+1}$, $P_n(a)$ is the Gaussian measure of the cone $\{x:a|(x_1,\dots,x_n)|<x_0\}$ and $M_n(a)$ is its first moment $\int x_0$. A set $K$ is a cone if $rx\in K\iff x\in K$ for all $r>0$. Let $K\subseteq\mathbb R^{n+1}$ be a measurable cone and $a\ge0$, and put $\rho=R(n+1,\frac12)/R(n,\frac12)$. Then
--   $$
--   \int_Kx_0\,d\gamma\le M_n(a)+\frac a{\sqrt{1+a^2}}\,\rho\,\bigl(\gamma(K)-P_n(a)\bigr).
--   $$
--
--   Among cones of given mass, the circular cone around the axis has the largest first moment.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CapBounds.lean#L145-L178

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
open Coords OneCell ProbabilityBounds Polar
open scoped Topology
variable {n : ℕ}

theorem OAI.GaussianPropeller.Cap.moment_rearrange (K : Set (CE (n+1))) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) {a : ℝ} (ha : 0≤a) :
    (∫ x : CE (n+1), K.indicator (fun x=>x 0) x ∂stdGaussian (CE (n+1))) ≤
      capM n a + a/Real.sqrt (1+a^2) * (radial (n+1) (1/2)/radial n (1/2)) *
        ((stdGaussian (CE (n+1))).real K-capP n a) := by sorry
