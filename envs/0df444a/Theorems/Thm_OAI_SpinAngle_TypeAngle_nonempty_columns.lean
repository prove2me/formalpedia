-- Prove2me | Theorems.Thm_OAI_SpinAngle_TypeAngle_nonempty_columns
-- name    : OAI.SpinAngle.TypeAngle.nonempty_columns
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:22:44.774624+00:00
-- url     : https://prove2.me/theorems/652bd24a-ec5f-4306-80a5-1e8cafea05bd
-- title:
--   Angle bound for column, row and global type projections on a board with at least one column
-- statement:
--   Fix an integer $q\ge1$, the signed spin alphabet $S_q=\{1,\dots,q\}\times\{0,1\}$ (even sector $0$, odd sector $1$) and the group $G=U(q)\times U(q)$. Recall the following notions.
--
--   - A *type label* $D=(a,b)$ is a pair of Young diagrams with at most $q$ rows each. Its entropy is $\mathrm{Ent}(D)=N\log N-\sum_kn_k\log n_k$ for the $2q$ row lengths $n=(a_1,\dots,a_q,b_1,\dots,b_q)$, with $N=\sum_kn_k$ and $0\log0=0$. Its dimension $\dim D$ is the dimension of $V_a\otimes V_b$, where $V_\lambda\subseteq(\mathbb{C}^q)^{\otimes\lambda}$ (one factor per cell of $\lambda$) is the irreducible polynomial $U(q)$-representation spanned by the vectors $g^{\otimes\lambda}h_\lambda$, $g\in U(q)$, and $h_\lambda$ is the column-antisymmetrization of the basis tensor that colours each cell by its row.
--   - For a finite set $\sigma$, $G$ acts on $X_\sigma=(\mathbb{C}^{S_q})^{\otimes\sigma}$ by $(g_0,g_1)\mapsto(g_0\oplus g_1)^{\otimes\sigma}$ ($g_0$ on the even sector, $g_1$ on the odd sector), and $P^{\sigma}_D$ is the orthogonal projection onto the isotypic component of type $V_a\otimes V_b$ (on which $G$ acts by $g_0^{\otimes a}\otimes g_1^{\otimes b}$), i.e. onto the span of the images of all $G$-intertwiners $V_a\otimes V_b\to X_\sigma$.
--
--   Let $R$ and $C$ be finite sets with $C$ nonempty and let $W\subseteq R\times C$ be a set of cells. For $j\in C$ and $i\in R$ let $W^{j}$ and $W_i$ be the sets of cells of $W$ in column $j$ and in row $i$, and $o_i=|W_i|$. Let $D$ be a type label, $H=(H_j)_{j\in C}$ a family of column labels and $K=(K_i)_{i\in R}$ a family of row labels. On $X_W=\bigotimes_{j\in C}X_{W^{j}}=\bigotimes_{i\in R}X_{W_i}$ consider the orthogonal projections
--   $$P_H=\bigotimes_{j\in C}P^{W^{j}}_{H_j},\qquad P_K=\bigotimes_{i\in R}P^{W_i}_{K_i},\qquad P_D=P^{W}_D ,$$
--   and put $\mathrm{Ent}(H)=\sum_j\mathrm{Ent}(H_j)$, $\dim H=\prod_j\dim H_j$, likewise $\mathrm{Ent}(K)$ and $\dim K$, and
--   $$\varphi(W)=\prod_{i\in R,\ o_i\ge1}\Big(\frac{|C|}{o_i}\Big)^{o_i}.$$
--
--   **Theorem.** With the operator norm on $X_W$,
--   $$\big\|P_H\,P_K\,P_D\big\|^{2}\le\min\Big\{1,\ e^{\mathrm{Ent}(H)+\mathrm{Ent}(K)-\mathrm{Ent}(D)}\,\dim H\,\dim K\;\varphi(W)\Big\}.$$
--
--   No relation between the sizes of the labels and the numbers of cells is assumed. In words, the composition of the column-type, row-type and global-type projections is exponentially small in the entropy deficit $\mathrm{Ent}(D)-\mathrm{Ent}(H)-\mathrm{Ent}(K)$, up to the factor $\dim H\,\dim K$ and the missing-cell factor $\varphi(W)$, which equals $1$ when $W=R\times C$.
--
--   **Formalization Note** The three projections are `TypeBlocks.projection (column W) H`, `TypeBlocks.projection (row W) K` and `D.projection W`, where `column W` and `row W` send a cell to its column and its row and the block tensor product runs over their fibres. $\varphi(W)$ is `phi W = missingCellProductFactor (Fintype.card C) (missingInRow W)`, the norm is the operator norm of matrices indexed by functions `W → Fin q × Bool`, and the assumptions `[Nonempty C]` and `[Nonempty (Fin q)]` are part of the statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/SpinAngle/TypeAngle.lean#L105-L156

import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_TypeAngle

open OAI OAI.SpinAngle OAI.SpinAngle.TypeAngle
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
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open MatrixAnalysis TensorMatrix
variable {q : ℕ} [contextInstance30_17 : Nonempty (Fin q)]
variable {R C : Type*} [contextInstance31_23 : Fintype R] [contextInstance31_35 : DecidableEq R] [contextInstance31_51 : Fintype C] [contextInstance31_63 : DecidableEq C]

theorem OAI.SpinAngle.TypeAngle.nonempty_columns [Nonempty C] (W : Finset (R × C))
    (D : TypeLabel q) (H : C → TypeLabel q) (K : R → TypeLabel q) :
    ‖TypeBlocks.projection (column W) H * TypeBlocks.projection (row W) K * D.projection W‖ ^ 2 ≤
      min 1 (Real.exp (TypeBlocks.entropy H + TypeBlocks.entropy K - D.entropy) *
        (TypeBlocks.dimension H : ℝ) * (TypeBlocks.dimension K : ℝ) * phi W) := by sorry
