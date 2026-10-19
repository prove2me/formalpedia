-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_configuration_determinants
-- name    : OAI.GaussianPropeller.Reduction.configuration_determinants
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:51:09.634528+00:00
-- url     : https://prove2.me/theorems/2db0d2f4-7a76-4a23-bd2f-33e0b6968b5a
-- title:
--   Determinant inequalities among four or more centroids
-- statement:
--   Let $z_1,\dots,z_k$ sum to zero and be pairwise obtuse, and $z_i\ne0$. For $z\ne0$ and $y$, the residual of $y$ along $z$ is $y+c\,z$ with coefficient $c=-\langle z,y\rangle/|z|^2$, the component of $y$ orthogonal to $z$. Assume for all $a,b\ne i$ the pair inequality: the Gram determinant of the residuals of $z_a,z_b$ along $z_i$ is at most $(3/\pi)^2|z_i|^2(1+c_a)^2(1+c_b)^2$, where $c_a,c_b$ are the coefficients. Let $j,l,q$ be distinct and different from $i$ with $|z_i|\le|z_q|\le|z_j|,|z_l|$. Then
--   $$
--   \bigl(|z_q|^2-|z_i|^2\bigr)\bigl(|z_j|^2+|z_l|^2-|z_q|^2-2|z_i|^2\bigr)\le8\Bigl(\frac3\pi\Bigr)^2|z_i|^2,
--   $$
--   and $\frac32\bigl(|z_q|^2-|z_i|^2\bigr)^2\le10(3/\pi)^2|z_i|^2$.
--
--   A short centroid forces all other centroids to have nearly equal lengths.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/FourReduction.lean#L160-L212

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
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
variable {d k:ℕ}

theorem OAI.GaussianPropeller.Reduction.configuration_determinants (z:Fin k→Space d) (hsum:∑ j,z j=0)
    (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hi:z i≠0)
    {j l q : Fin k} (hij:i≠j) (hil:i≠l) (hiq:i≠q) (hjl:j≠l) (hjq:j≠q) (hlq:l≠q)
    (hj:‖z q‖≤‖z j‖) (hl:‖z q‖≤‖z l‖) (hmin:‖z i‖≤‖z q‖)
    (hpair:∀ a b, i≠a → i≠b →
      ‖residualVector (z i) (z a)‖^2*‖residualVector (z i) (z b)‖^2-
      ⟪residualVector (z i) (z a),residualVector (z i) (z b)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z a))^2*
      (1+residualCoefficient (z i) (z b))^2) :
    (‖z q‖^2-‖z i‖^2)*(‖z j‖^2+‖z l‖^2-‖z q‖^2-2*‖z i‖^2)≤
      8*(3/Real.pi)^2*‖z i‖^2 ∧
    (3/2:ℝ)*(‖z q‖^2-‖z i‖^2)^2≤10*(3/Real.pi)^2*‖z i‖^2 := by sorry
