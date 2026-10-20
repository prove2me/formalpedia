-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_minimum_le_root
-- name    : OAI.GaussianPropeller.Scalar.RadiusData.minimum_le_root
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:24:59.974646+00:00
-- url     : https://prove2.me/theorems/ae2a98df-86bf-4e36-ad34-da4142c51f16
-- title:
--   The smallest radius lies below the small root
-- statement:
--   Fix $A$ and let the charge be $c_A(u)=0.415\,u-(A-0.15)\,u^2$. Radius data of length $m$ consist of radii $r_0\ge r_1\ge\dots\ge r_{m-1}>0$, each at most $\frac23$, with $\sum_ir_i^2=1$. They come with budgets $\delta_i\ge0$ such that $c_A(r_i)\le\delta_i$ and $\sum_i\delta_i=1-A$. The admissible regime for $(A,k)$ is a list of numerical conditions, including $0.884\le A<1$ and $k\ge2$; it defines a small root $u_0<0.12$ of $k\,c_A(u)=1-A$. Assume $(A,k)$ is admissible, $m\ge5$, $3+k\le m$ and $r_{m-1}>0.066$. Then
--   $$
--   r_{m-1}\le u_0 .
--   $$
--
--   Since $u_0<0.12$, the shortest normalized centroid of a counterexample with many cells is short.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Scalar.lean#L493-L509

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

theorem OAI.GaussianPropeller.Scalar.RadiusData.minimum_le_root {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (hkm : 3 + k ≤ m) (ht : 0.066 < D.r (m - 1)) :
    D.r (m - 1) ≤ smallRoot A k := by sorry
