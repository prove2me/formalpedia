-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_common_charge
-- name    : OAI.GaussianPropeller.Scalar.RadiusData.common_charge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:22:35.932893+00:00
-- url     : https://prove2.me/theorems/328fb79a-897f-474c-9a4a-4f5c75b05d99
-- title:
--   Charge of the radii beyond the first two
-- statement:
--   Fix $A$ and let the charge be $c_A(u)=0.415\,u-(A-0.15)\,u^2$. Radius data of length $m$ consist of radii $r_0\ge r_1\ge\dots\ge r_{m-1}>0$, each at most $\frac23$, with $\sum_ir_i^2=1$. They come with budgets $\delta_i\ge0$ such that $c_A(r_i)\le\delta_i$ and $\sum_i\delta_i=1-A$. They model the normalized centroid lengths of a counterexample with $m$ cells. If $m\ge3$ and $A\ge0.884$, then
--   $$
--   \bigl(1-(r_0^2+r_1^2)\bigr)\Bigl(\frac{0.415}{r_2}-0.734\Bigr)\le0.116 .
--   $$
--
--   If the two longest centroids leave much squared length to the others, the third radius cannot be too small.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Scalar.lean#L338-L370

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

theorem OAI.GaussianPropeller.Scalar.RadiusData.common_charge (hm : 3 ≤ m) (hA : 0.884 ≤ A) :
    (1 - (D.r 0 ^ 2 + D.r 1 ^ 2)) * (0.415 / D.r 2 - 0.734) ≤ 0.116 := by sorry
