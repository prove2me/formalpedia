-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_minimal_residual_pair
-- name    : OAI.GaussianPropeller.Reduction.minimal_residual_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:35:29.670992+00:00
-- url     : https://prove2.me/theorems/c8f2d086-1a63-4301-8e2e-81371e5da3a5
-- title:
--   The pair inequality for a minimal optimal partition
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. A partition into $k$ cells is a family of measurable sets $A_1,\dots,A_k$ such that almost every point lies in exactly one of them. The centroid of $A$ is $z(A)=\int_Ax\,d\gamma_d$, and the value of the partition is $V=\sum_i|z(A_i)|^2$. A minimal optimal partition maximizes $V$ and, among maximizers, has the fewest cells of positive measure. For $z\ne0$ and $y$, the residual of $y$ along $z$ is $y+c\,z$ with $c=-\langle z,y\rangle/|z|^2$, the component of $y$ orthogonal to $z$. Let $A$ be minimal optimal with positive value, and let $i,j,l$ be indices of positive-mass cells with $i\ne j$ and $i\ne l$. Let $z=z(A_i)$, let $r,s$ be the residuals of $z(A_j),z(A_l)$ along $z$, and $a,b$ the corresponding coefficients. Then
--   $$
--   \sqrt{|r|^2|s|^2-\langle r,s\rangle^2}\le\frac{9\,|z|\,(1+a)(1+b)}{2\pi\sqrt{2\pi}} .
--   $$
--
--   This is the pair condition in the definition of a configuration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/ResidualBounds.lean#L96-L136

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

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
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
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

theorem OAI.GaussianPropeller.Reduction.minimal_residual_pair {A : Fin k → Set (Space d)} (hA : MinimalOptimal A)
    (hpos : 0 < value A) {i j l : Fin k}
    (hi : gaussian d (A i) ≠ 0) (hj : gaussian d (A j) ≠ 0)
    (hl : gaussian d (A l) ≠ 0) (hij : i ≠ j) (hil : i ≠ l) :
    let z := centroid (A i)
    let r := residualVector z (centroid (A j))
    let s := residualVector z (centroid (A l))
    Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
      9*‖z‖*(1+residualCoefficient z (centroid (A j)))*
        (1+residualCoefficient z (centroid (A l)))/(2*Real.pi*Real.sqrt (2*Real.pi)) := by sorry
