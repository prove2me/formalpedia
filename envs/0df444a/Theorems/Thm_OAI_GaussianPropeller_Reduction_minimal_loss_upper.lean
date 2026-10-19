-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_minimal_loss_upper
-- name    : OAI.GaussianPropeller.Reduction.minimal_loss_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:17:40.748719+00:00
-- url     : https://prove2.me/theorems/ac3e8f0e-9186-4e16-9746-137eabc5d835
-- title:
--   Upper bound for the winning margin of a cell
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$, $z(A)=\int_Ax\,d\gamma_d$ the centroid of a set and $\sum_i|z(A_i)|^2$ the value of a partition. Let $\varphi$ and $\Phi$ be the standard normal density and distribution function, and $q=\Phi^{-1}$. Let $A$ be a minimal optimal partition into $k\ge2$ cells, all of positive measure, with positive value and centroids $z_j=z(A_j)$. Then for each $i$, writing $P=\gamma_d(A_i)$ and $a=\Phi^{-1}(P)$,
--   $$
--   \int\Bigl(\langle z_i,x\rangle-\max_{j\ne i}\langle z_j,x\rangle\Bigr)_+\,d\gamma_d\le\frac k{k-1}\,\varphi(a)\bigl(a\,P+\varphi(a)\bigr).
--   $$
--
--   Combined with the lower bound on the same margin, this ties each cell's centroid length to its mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/ConeReduction.lean#L70-L129

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
open Set GaussianPropeller.Quantile
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

theorem OAI.GaussianPropeller.Reduction.minimal_loss_upper (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    (∫ x, max (⟪centroid (A i),x⟫ -
      omittedMax hk (fun j => centroid (A j)) i x) 0 ∂gaussian d) ≤
      ((k:ℝ)/((k:ℝ)-1)) * φ (q ((gaussian d).real (A i))) *
      (q ((gaussian d).real (A i)) * (gaussian d).real (A i)+φ (q ((gaussian d).real (A i)))) := by sorry
