-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_realCriterion_lattice
-- name    : OAI.EuclideanRamsey.realCriterion_lattice
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:17:00.49846+00:00
-- url     : https://prove2.me/theorems/ded493db-c52b-4285-bdc1-cedf57828e4c
-- title:
--   The real tensor criterion yields a rational lattice presentation with $UCU^{\top}=I$
-- statement:
--   Let $s,d\in\mathbb N$ with $d\ge1$ and let $a_1,\dots,a_s\in\mathbb R^d$. Index the coordinates of $\mathbb R^{1+d}$ by $\{0,1,\dots,d\}$, and let $\hat a_i=(1,a_{i1},\dots,a_{id})$ be the augmented vectors; for $w\in\mathbb R^{1+d}$ write $\langle\hat a_i,w\rangle=w(0)+\sum_{\alpha=1}^da_{i\alpha}w(\alpha)$. Let $\mathbb R\otimes_{\mathbb Q}\mathbb R$ be the tensor product of $\mathbb R$ with itself over $\mathbb Q$ (a commutative ring) and $\mathrm m:\mathbb R\otimes_{\mathbb Q}\mathbb R\to\mathbb R$, $x\otimes y\mapsto xy$, the multiplication map. The configuration satisfies the *real tensor criterion* if there is a $(1+d)\times(1+d)$ matrix $P=(P_{\alpha\beta})_{\alpha,\beta=0}^{d}$ with entries in $\mathbb R\otimes_{\mathbb Q}\mathbb R$ such that
--   $$\sum_{\alpha,\beta=0}^d(\hat a_{i\alpha}\otimes1)\,P_{\alpha\beta}\,(1\otimes\hat a_{i\beta})=0\quad(1\le i\le s),\qquad\mathrm m(P_{\alpha\beta})=\delta_{\alpha\beta}\quad(1\le\alpha,\beta\le d).$$
--
--   **Theorem.** If $a$ satisfies the real tensor criterion, then there exist $k\ge1$, vectors $w_1,\dots,w_k\in\mathbb R^{1+d}$ and a symmetric rational $k\times k$ matrix $C$ with the following properties. Let $U$ be the real $d\times k$ matrix of spatial coordinates, $U_{\alpha j}=w_j(\alpha)$ for $1\le\alpha\le d$. Then
--   $$UCU^{\top}=I_d ,$$
--   and for every $i$, setting
--   $$\Lambda_i=\Bigl\{\gamma\in\mathbb Z^k:\ \sum_{j=1}^k\gamma_j\,\langle\hat a_i,w_j\rangle=0\Bigr\}$$
--   and letting $L_i\subseteq\mathbb Q^k$ be the $\mathbb Q$-linear span of $\Lambda_i$, the tensor $\widehat C=\sum_{a,b}C_{ab}\,e_a\otimes e_b\in\mathbb Q^k\otimes_{\mathbb Q}\mathbb Q^k$ has zero image in $(\mathbb Q^k/L_i)\otimes_{\mathbb Q}(\mathbb Q^k/L_i)$.
--
--   The theorem replaces the tensor data $P$, which lives in the huge ring $\mathbb R\otimes_{\mathbb Q}\mathbb R$, by finite rational data: the lattice $\mathbb Z^k$, its subgroups $\Lambda_i$ of integer relations among the real numbers $\langle\hat a_i,w_j\rangle$, and the matrix $C$. These are exactly the hypotheses of the finite lattice identity, and the normalization $UCU^{\top}=I_d$ is what later turns second moments proportional to $C$ into an isotropic Gram matrix in $\mathbb R^d$.
--
--   **Formalization Note** The criterion is `RealCriterion a`; the index set is `Option (Fin d)` with `none` playing the role of coordinate $0$, and the entries lie in `ℝ ⊗[ℚ] ℝ`. The vectors $w_j$ have type `AffineVector d = Option (Fin d) → ℝ`. The subgroup $\Lambda_i$ is the kernel of the additive map `((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize`, and the quotient condition is `quotientTensor Λ_i (matrixTensor C) = 0`. In $UCU^{\top}$ the entries of $C$ are cast to real numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/TensorPresentation.lean#L224-L255

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

open OAI OAI.EuclideanRamsey
universe uVector
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
open scoped TensorProduct RealInnerProductSpace
open scoped TensorProduct BigOperators
open scoped TensorProduct
open scoped TensorProduct BigOperators

theorem OAI.EuclideanRamsey.realCriterion_lattice {s d : ℕ} (a : Fin s → Space d) (hd : 1 ≤ d)
    (h : RealCriterion a) :
    ∃ (k : ℕ) (w : Fin k → AffineVector d) (C : Matrix (Fin k) (Fin k) ℚ),
      1 ≤ k ∧ C.IsSymm ∧
      (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)) * (C.map (Rat.cast : ℚ → ℝ)) *
        (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)).transpose = (1 : Matrix (Fin d) (Fin d) ℝ) ∧
      ∀ i,quotientTensor
        (AddMonoidHom.ker (((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize))
        (matrixTensor C) = 0 := by sorry
