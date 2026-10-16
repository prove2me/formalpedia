-- Prove2me | Theorems.Thm_OAI_Paper256_BlockPencil_normalized_exists
-- name    : OAI.Paper256.BlockPencil.normalized_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:20:48.969158+00:00
-- url     : https://prove2.me/theorems/a147d6b7-3de6-4fd9-a3e6-608f1852692f
-- title:
--   A unital block pencil satisfying the slice condition yields a normalized Schur-complement pencil
-- statement:
--   Write $\mathrm{Sym}_k$ for the real vector space of symmetric $k\times k$ real matrices. For a symmetric matrix $M$ write $M\succeq0$ if $M$ is positive semidefinite ($v^\top Mv\ge0$ for all real vectors $v$) and $M\succ0$ if it is positive definite ($v^\top Mv>0$ for all $v\neq0$).
--
--   For $y=(y_1,y_2,y_3)\in\mathbb{R}^3$ let $Q(y)$ be the symmetric $3\times3$ matrix with diagonal entries $Q(y)_{ii}=y_i^2+y_{i+1}^2$ (indices modulo $3$) and off-diagonal entries $Q(y)_{ij}=-y_iy_j$. For a real $4\times4$ matrix $M$ with rows and columns indexed by $0,1,2,3$, write $p=(M_{0j})_{j=1}^3$, $q=(M_{i0})_{i=1}^3$ and $M'=(M_{ij})_{i,j=1}^3$, and define
--   $$\varphi_y(M)=\begin{pmatrix}\operatorname{tr}\bigl(Q(y)M'\bigr)&-p^\top Q(y)\\-Q(y)\,q&M_{00}\,Q(y)\end{pmatrix}.$$
--   The matrix $\varphi_y(M)$ is linear in $M$ and homogeneous of degree two in $y$.
--
--   A *unital block pencil* for a set $K\subseteq\mathcal A=\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$ (points written $(X,Z,y)$) consists of integers $a,c\ge1$ and linear maps
--   $$D,F:\mathrm{Sym}_4\to\mathrm{Sym}_a,\quad E:\mathrm{Sym}_4\to\mathrm{Sym}_c,\quad C:\mathrm{Sym}_4\to\mathbb{R}^{a\times c},\quad A:\mathbb{R}^3\to\mathrm{Sym}_a,\quad B:\mathbb{R}^3\to\mathbb{R}^{a\times c},\quad G:\mathbb{R}^3\to\mathrm{Sym}_c$$
--   such that $D$ and $E$ are positive (they send positive semidefinite matrices to positive semidefinite matrices), $D(I_4)=I_a$, $E(I_4)=I_c$, and for all $(X,Z,y)\in\mathcal A$
--   $$(X,Z,y)\in K\iff\begin{pmatrix}D(X)+F(Z)+A(y)&C(Z)+B(y)\\ (C(Z)+B(y))^\top&E(Z)+G(y)\end{pmatrix}\succeq0 .$$
--
--   A *normalized pencil* consists of integers $a,c\ge1$ and linear maps $D:\mathrm{Sym}_4\to\mathrm{Sym}_a$, $E:\mathrm{Sym}_4\to\mathrm{Sym}_c$ and $B:\mathbb{R}^3\to\mathbb{R}^{a\times c}$ such that $D$ and $E$ are positive, $D(I_4)=I_a$, $E(I_4)=I_c$, and for all $X,Z\in\mathrm{Sym}_4$ and $y\in\mathbb{R}^3$ with $X\succ0$
--   $$Z-\varphi_y(X^{-1})\succeq0\iff E(Z)-B(y)^\top D(X)^{-1}B(y)\succeq0 .$$
--
--   **Theorem.** If $K\subseteq\mathcal A$ carries a unital block pencil and satisfies the *slice condition*: for all $X,Z\in\mathrm{Sym}_4$ and $y\in\mathbb{R}^3$ with $X\succ0$,
--   $$(X,Z,y)\in K\iff Z-\varphi_y(X^{-1})\succeq0 ,$$
--   then a normalized pencil exists.
--
--   In the argument that the hyperbolicity cone in $\mathcal A$ is not a spectrahedron, this is the final normalization step: a spectrahedral representation of the cone leads to unital positive maps $D,E$ and a linear map $B$ that describe the slice condition uniformly through a Schur complement. The contradiction is then derived from this normalized description.
--
--   **Formalization Note** Points of $\mathcal A$ are pairs `((X, Z), y)` of type `Ambient`; the unital block pencil is the structure `BlockPencil K` with fields `a c D E F C A B G`, positivity fields `D_positive`, `E_positive`, unitality fields `D_unital`, `E_unital` and the field `represents`. The map $\varphi_y$ is `phi y` (built from `qMatrix y`), and $X^{-1}$ is Mathlib's matrix inverse, which is the genuine inverse here because $X\succ0$. The normalized pencil is the structure `NormalizedPencil`, whose equivalence field is `schur_equivalence`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PencilRecovery.lean#L70-L93

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit

open OAI OAI.Paper256 OAI.Paper256.BlockPencil
open Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator

theorem OAI.Paper256.BlockPencil.normalized_exists {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef)) :
    Nonempty NormalizedPencil := by sorry
