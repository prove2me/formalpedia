-- Prove2me | Theorems.Thm_OAI_Paper256_NormalizedPencil_positive_threshold
-- name    : OAI.Paper256.NormalizedPencil.positive_threshold
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:46:11.900991+00:00
-- url     : https://prove2.me/theorems/38ff720f-93ef-4ba9-a24d-b778710064b4
-- title:
--   Operator-norm threshold identity for normalized Schur pencils
-- statement:
--   Throughout, $\mathrm{Sym}_n$ is the space of real symmetric $n\times n$ matrices, $I$ (or $I_n$) is the identity matrix, $M\succeq 0$ (resp. $M\succ 0$) means that $M$ is positive semidefinite (resp. positive definite), and $\|M\|$ is the spectral norm of a real, possibly rectangular, matrix, i.e. its operator norm as a linear map between Euclidean spaces. For $M\succ 0$, $M^{-1/2}$ denotes the inverse of the positive definite square root of $M$.
--
--   For $y=(y_0,y_1,y_2)\in\mathbb{R}^3$ (indices read modulo $3$) let $Q(y)\in\mathrm{Sym}_3$ have entries $Q(y)_{ii}=y_i^2+y_{i+1}^2$ and $Q(y)_{ij}=-y_iy_j$ for $i\ne j$. For a real $4\times 4$ matrix written in block form $M=\begin{pmatrix} m & r^{\top}\\ s & M'\end{pmatrix}$ with $m\in\mathbb{R}$, $r,s\in\mathbb{R}^3$ and $M'\in\mathbb{R}^{3\times 3}$, define the $4\times 4$ matrix
--   $$
--   \varphi_y(M)=\begin{pmatrix}\operatorname{tr}\bigl(Q(y)M'\bigr) & -r^{\top}Q(y)\\ -Q(y)\,s & m\,Q(y)\end{pmatrix}.
--   $$
--
--   A *normalized pencil* $P=(a,c,D,E,B)$ consists of positive integers $a,c$ and linear maps $D:\mathrm{Sym}_4\to\mathrm{Sym}_a$, $E:\mathrm{Sym}_4\to\mathrm{Sym}_c$ and $B:\mathbb{R}^3\to\mathbb{R}^{a\times c}$ such that $D$ and $E$ are positive (they send positive semidefinite matrices to positive semidefinite matrices), unital ($D(I_4)=I_a$ and $E(I_4)=I_c$), and satisfy the Schur-complement equivalence: for all $X,Z\in\mathrm{Sym}_4$ and $y\in\mathbb{R}^3$ with $X\succ 0$,
--   $$
--   Z-\varphi_y(X^{-1})\succeq 0\iff E(Z)-B(y)^{\top}D(X)^{-1}B(y)\succeq 0.
--   $$
--
--   **Statement.** Let $P=(a,c,D,E,B)$ be a normalized pencil, let $X,Z\in\mathrm{Sym}_4$ and $y\in\mathbb{R}^3$, and assume $X\succ 0$, $Z\succ 0$, $D(X)\succ 0$ and $E(Z)\succ 0$. Then
--   $$
--   \bigl\|Z^{-1/2}\,\varphi_y(X^{-1})\,Z^{-1/2}\bigr\|=\bigl\|D(X)^{-1/2}\,B(y)\,E(Z)^{-1/2}\bigr\|^{2}.
--   $$
--
--   The defining property of a normalized pencil is an equivalence between two matrix inequalities; this theorem converts it into an exact equality between two real numbers, which is stable under limits. It is used along paths of positive definite matrices $X$, $Z$ that degenerate towards rank-one projections, which produces the rank-one norm identity relating the pencil to the Choi–Lam form.
--
--   **Formalization Note** The matrix $M^{-1/2}$ is `inverseSquareRoot M`, defined for every symmetric $M=U\operatorname{diag}(\lambda_i)U^{\top}$ as $U\operatorname{diag}\bigl((\sqrt{\lambda_i})^{-1}\bigr)U^{\top}$; under the positive definiteness hypotheses it is the usual inverse square root. The norms are the $\ell^2$ operator norms of `Matrix.Norms.L2Operator`. The hypotheses $D(X)\succ 0$ and $E(Z)\succ 0$ are stated separately, although they can also be derived from $X\succ 0$, $Z\succ 0$ and the positivity and unitality of $D$ and $E$. `NormalizedPencil` packages $(a,c,D,E,B)$ together with the positivity, unitality and Schur-equivalence fields; `phi y M` is $\varphi_y(M)$ and `qMatrix y` is $Q(y)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/NormCongruence.lean#L34-L60

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
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic

open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix

theorem OAI.Paper256.NormalizedPencil.positive_threshold (P : NormalizedPencil)
    (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hX : (X : Mat 4 ℝ).PosDef) (hZ : (Z : Mat 4 ℝ).PosDef)
    (hDX : (P.D X : Mat P.a ℝ).PosDef) (hEZ : (P.E Z : Mat P.c ℝ).PosDef) :
    ‖inverseSquareRoot Z * phi y (X : Mat 4 ℝ)⁻¹ * inverseSquareRoot Z‖ =
      ‖inverseSquareRoot (P.D X) * P.B y * inverseSquareRoot (P.E Z)‖ ^ 2 := by sorry
