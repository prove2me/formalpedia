-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_minimum_charge_bound
-- name    : OAI.GaussianPropeller.Scalar.RadiusData.minimum_charge_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:24:13.134531+00:00
-- url     : https://prove2.me/theorems/239e5d4b-82d3-47e6-bce0-a040d3670b98
-- title:
--   The charge of the smallest radius is bounded by the budget
-- statement:
--   Fix $A$ and let the charge be $c_A(u)=0.415\,u-(A-0.15)\,u^2$. Radius data of length $m$ consist of radii $r_0\ge r_1\ge\dots\ge r_{m-1}>0$, each at most $\frac23$, with $\sum_ir_i^2=1$. They come with budgets $\delta_i\ge0$ such that $c_A(r_i)\le\delta_i$ and $\sum_i\delta_i=1-A$. They model the normalized centroid lengths of a counterexample with $m$ cells. Assume $(A,k)$ is in the admissible regime and that $m\ge5$, $3+k\le m$ and $r_{m-1}>0.066$. Then
--   $$
--   k\,c_A(r_{m-1})\le1-A .
--   $$
--
--   So the smallest radius lies below the small root of $k\,c_A(u)=1-A$, which drives the contradiction for five or more cells.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Scalar.lean#L475-L491

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
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry
import Definitions.Def_OAI_Probability_GaussianPropeller_QuarticCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_Scalar

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Scalar OAI.GaussianPropeller.Scalar.RadiusData
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
variable {m : ℕ} {A : ℝ} (D : RadiusData m A)

theorem OAI.GaussianPropeller.Scalar.RadiusData.minimum_charge_bound {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (hkm : 3 + k ≤ m) (ht : 0.066 < D.r (m - 1)) :
    (k : ℝ) * charge A (D.r (m - 1)) ≤ 1 - A := by sorry
