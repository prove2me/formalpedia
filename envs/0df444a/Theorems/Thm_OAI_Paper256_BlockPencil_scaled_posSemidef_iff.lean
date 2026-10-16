-- Prove2me | Theorems.Thm_OAI_Paper256_BlockPencil_scaled_posSemidef_iff
-- name    : OAI.Paper256.BlockPencil.scaled_posSemidef_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:18:09.633992+00:00
-- url     : https://prove2.me/theorems/a9793048-b60b-466c-a3da-b5e920f45d61
-- title:
--   Rescaled block matrices of a unital block pencil detect the slice condition
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
--   For such a pencil, $X,Z\in\mathrm{Sym}_4$, $y\in\mathbb{R}^3$ and $s\in\mathbb{R}$, define the *rescaled block matrix*
--   $$S_s(X,Z,y)=\begin{pmatrix}D(X)+s\,A(y)+s^2F(Z)&B(y)+s\,C(Z)\\ (B(y)+s\,C(Z))^\top&E(Z)\end{pmatrix}.$$
--
--   **Theorem.** Let $K\subseteq\mathcal A$ carry a unital block pencil as above, and assume that $K$ satisfies the *slice condition*: for all $X,Z\in\mathrm{Sym}_4$ and $y\in\mathbb{R}^3$ with $X\succ0$,
--   $$(X,Z,y)\in K\iff Z-\varphi_y(X^{-1})\succeq0 .$$
--   Then for all $X,Z\in\mathrm{Sym}_4$ with $X\succ0$, all $y\in\mathbb{R}^3$ and all real $s\neq0$,
--   $$S_s(X,Z,y)\succeq0\iff Z-\varphi_y(X^{-1})\succeq0 .$$
--
--   As $s\to0$ the matrix $S_s(X,Z,y)$ tends to $\begin{pmatrix}D(X)&B(y)\\B(y)^\top&E(Z)\end{pmatrix}$. The equivalence for every $s\neq0$ is what allows a limiting argument transferring the slice condition to this simpler block matrix, whose Schur complement then gives a normalized pencil.
--
--   **Formalization Note** Points of $\mathcal A$ are pairs `((X, Z), y)` of type `Ambient`; the unital block pencil is the structure `BlockPencil K` with fields `a c D E F C A B G`, positivity fields `D_positive`, `E_positive`, unitality fields `D_unital`, `E_unital` and the field `represents`. The map $\varphi_y$ is `phi y` (built from `qMatrix y`), and $X^{-1}$ is Mathlib's matrix inverse, which is the genuine inverse here because $X\succ0$. The rescaled matrix is `P.scaled X Z y s`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/BlockScaling.lean#L24-L46

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

open OAI OAI.Paper256 OAI.Paper256.BlockPencil
open Matrix Set
open scoped Matrix.Norms.L2Operator

theorem OAI.Paper256.BlockPencil.scaled_posSemidef_iff {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef) (s : ℝ) (hs : s ≠ 0) :
    (P.scaled X Z y s).PosSemidef ↔
      ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by sorry
