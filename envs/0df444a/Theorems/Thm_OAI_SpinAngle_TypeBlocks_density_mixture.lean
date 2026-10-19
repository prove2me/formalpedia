-- Prove2me | Theorems.Thm_OAI_SpinAngle_TypeBlocks_density_mixture
-- name    : OAI.SpinAngle.TypeBlocks.density_mixture
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:18:20.038895+00:00
-- url     : https://prove2.me/theorems/c03b4a0a-7102-42ef-b865-4f5f739ad481
-- title:
--   Block type projections are dominated by mixtures of product even-density states of total weight $e^{\mathrm{Ent}}\dim$
-- statement:
--   Fix an integer $q\ge1$, the signed spin alphabet $S_q=\{1,\dots,q\}\times\{0,1\}$ with even sector $0$ and odd sector $1$, and the compact group $G=U(q)\times U(q)$.
--
--   *Even densities.* An even density is a pair $A=(A_0,A_1)$ of positive semidefinite $q\times q$ complex matrices with $\operatorname{tr}A_0+\operatorname{tr}A_1=1$; its matrix is the block-diagonal density matrix $\rho(A)=A_0\oplus A_1$ on $\mathbb{C}^{S_q}$, with $A_0$ on the even and $A_1$ on the odd sector.
--
--   *Type labels.* A type label is a pair $D=(a,b)$ of Young diagrams, each with at most $q$ rows. Its entropy is $\mathrm{Ent}(D)=N\log N-\sum_kn_k\log n_k$, where $n=(a_1,\dots,a_q,b_1,\dots,b_q)$ lists the $2q$ row lengths, $N=\sum_kn_k=|a|+|b|$ and $0\log0=0$. For a Young diagram $\lambda$ with at most $q$ rows, $V_\lambda\subseteq(\mathbb{C}^q)^{\otimes\lambda}$ (one tensor factor per cell) is the span of the vectors $g^{\otimes\lambda}h_\lambda$, $g\in U(q)$, where $h_\lambda$ is the antisymmetrization over column-preserving permutations of cells of the basis tensor colouring each cell by its row; this is the irreducible polynomial representation of $U(q)$ with highest weight $\lambda$. The carrier of $D$ is $V_D=V_a\otimes V_b$, with $G$ acting by $(g_0,g_1)\mapsto g_0^{\otimes a}\otimes g_1^{\otimes b}$, and $\dim D=\dim_{\mathbb{C}}V_D$.
--
--   *Type projections.* For a finite set $\sigma$ let $X_\sigma=(\mathbb{C}^{S_q})^{\otimes\sigma}$, with $G$ acting by $(g_0,g_1)\mapsto(g_0\oplus g_1)^{\otimes\sigma}$. The type projection $P^{\sigma}_D$ is the orthogonal projection of $X_\sigma$ onto the isotypic component of type $V_D$, i.e. onto the span of the images $L(V_D)$ of all $G$-intertwiners $L:V_D\to X_\sigma$.
--
--   *Blocks.* Let $\tau$ and $J$ be finite sets, $f:\tau\to J$ a map, and $D=(D_j)_{j\in J}$ a family of type labels. Under the identification $X_\tau=\bigotimes_{j\in J}X_{f^{-1}(j)}$ put
--   $$P_{f,D}=\bigotimes_{j\in J}P^{f^{-1}(j)}_{D_j},\qquad \mathrm{Ent}(D)=\sum_{j\in J}\mathrm{Ent}(D_j),\qquad \dim D=\prod_{j\in J}\dim D_j .$$
--
--   **Theorem.** There exist a finite index set $I$, real weights $w_i\ge0$ and even densities $R_i(j)$ ($i\in I$, $j\in J$) such that
--   $$\sum_{i\in I}w_i=e^{\mathrm{Ent}(D)}\dim D\qquad\text{and}\qquad P_{f,D}\preceq\sum_{i\in I}w_i\bigotimes_{t\in\tau}\rho\big(R_i(f(t))\big),$$
--   where $\preceq$ is the Loewner order of Hermitian operators on $X_\tau$.
--
--   No compatibility between the sizes of the labels and the sizes of the fibres $f^{-1}(j)$ is assumed. The theorem dominates a block product of type projections by a mixture of product states that are constant along each block, at the price of the total weight $e^{\mathrm{Ent}(D)}\dim D$. Combined with norm bounds for product states it yields upper bounds for norms of products of type projections, such as the angle between column, row and global type projections on a board of cells.
--
--   **Formalization Note** $P_{f,D}$ is `TypeBlocks.projection f D`, built with `BlockTensor.tensor` from the matrices `(D j).projection (Fiber f j)`; each of these is the matrix of `Isotypic.projection`, the orthogonal projection onto `Isotypic.space`. $\mathrm{Ent}(D)$ and $\dim D$ are `TypeBlocks.entropy D` and `TypeBlocks.dimension D`. The index type $I$ lives in the same universe as $J$, the order is the Loewner order of `MatrixOrder`, and `TensorMatrix.tensor` is the Kronecker product. The standing assumption `[Nonempty (Fin q)]` encodes $q\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/SpinAngle/Core.lean#L4751-L4790

import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core

open OAI OAI.SpinAngle OAI.SpinAngle.TypeBlocks
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open SpinAngle.Young
universe u
open MatrixAnalysis
variable {q : ℕ}
variable {τ : Type*} {J : Type u} [contextInstance4383_34 : Fintype τ] [contextInstance4383_46 : DecidableEq τ] [contextInstance4383_62 : Fintype J] [contextInstance4383_74 : DecidableEq J]
variable [contextInstance4410_9 : Nonempty (Fin q)]

theorem OAI.SpinAngle.TypeBlocks.density_mixture (f : τ → J) (D : J → TypeLabel q) :
    ∃ (ι : Type u) (_ : Fintype ι) (w : ι → ℝ) (R : ι → J → EvenDensity q),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = Real.exp (entropy D) * (dimension D : ℝ)) ∧
      projection f D ≤ ∑ i, w i • TensorMatrix.tensor (fun t : τ => (R i (f t)).matrix) := by sorry
