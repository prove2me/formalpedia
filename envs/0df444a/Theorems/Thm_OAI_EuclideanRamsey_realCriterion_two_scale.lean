-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_realCriterion_two_scale
-- name    : OAI.EuclideanRamsey.realCriterion_two_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:20:21.361172+00:00
-- url     : https://prove2.me/theorems/1b2a0a06-d259-4101-bf49-12ec562162ec
-- title:
--   Configurations satisfying the real tensor criterion admit two-scale coordinate-permutation embeddings
-- statement:
--   Let $s\ge1$ and $d\ge1$, and let $a_1,\dots,a_s$ be points of the Euclidean space $\mathbb R^d$. Index the coordinates of $\mathbb R^{1+d}$ by $\{0,1,\dots,d\}$ and let $\hat a_i=(1,a_{i1},\dots,a_{id})$. Let $\mathbb R\otimes_{\mathbb Q}\mathbb R$ be the tensor product over $\mathbb Q$ and $\mathrm m(x\otimes y)=xy$ the multiplication map. Assume $a$ satisfies the *real tensor criterion*: there is a $(1+d)\times(1+d)$ matrix $P$ with entries in $\mathbb R\otimes_{\mathbb Q}\mathbb R$ such that
--   $$\sum_{\alpha,\beta=0}^d(\hat a_{i\alpha}\otimes1)\,P_{\alpha\beta}\,(1\otimes\hat a_{i\beta})=0\quad(1\le i\le s),\qquad\mathrm m(P_{\alpha\beta})=\delta_{\alpha\beta}\quad(1\le\alpha,\beta\le d).$$
--   Then for every $\eta>0$ there exist an integer $\ell\ge1$ and points $p_1,\dots,p_s$, $q_1,\dots,q_s$ of the Euclidean space $\mathbb R^\ell$ such that, for all $i,j$,
--   $$|p_i-p_j|^2=|a_i-a_j|^2,\qquad|q_i-q_j|^2=\frac{\eta}{1+\eta}\,|a_i-a_j|^2,$$
--   and for every $i$ there is a permutation $\sigma_i$ of the coordinate set $\{1,\dots,\ell\}$ with $q_i(\sigma_i(x))=p_i(x)$ for every coordinate $x$.
--
--   In words: a congruent copy $p$ of the configuration and a copy $q$ shrunk by the factor $\sqrt{\eta/(1+\eta)}$ can be placed in a common Euclidean space so that each point $q_i$ is a coordinate permutation of $p_i$. In the proof that the field criterion implies the Ramsey property, this is the geometric input; the field criterion is first shown to imply the real tensor criterion, and the scale $\eta$ is then taken small.
--
--   **Formalization Note** The criterion is `RealCriterion a`, with matrix index set `Option (Fin d)` (`none` is coordinate $0$) and entries in `ℝ ⊗[ℚ] ℝ`; $\mathbb R^m$ is `Space m = EuclideanSpace ℝ (Fin m)`, and coordinates of $\mathbb R^\ell$ are indexed by `Fin ℓ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/GramCompletion.lean#L251-L287

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows

open OAI OAI.EuclideanRamsey
universe uIndex uRow uColor
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators

theorem OAI.EuclideanRamsey.realCriterion_two_scale {s d : ℕ} (a : Fin s → Space d)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (h : RealCriterion a) (η : ℝ) (hη : 0 < η) :
    ∃ (ℓ : ℕ),1 ≤ ℓ ∧ ∃ (f g : Fin s → Space ℓ),
      (∀ i j,‖f i-f j‖^2=‖a i-a j‖^2) ∧
      (∀ i j,‖g i-g j‖^2=(η/(1+η))*‖a i-a j‖^2) ∧
      ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g i (σ x)=f i x := by sorry
