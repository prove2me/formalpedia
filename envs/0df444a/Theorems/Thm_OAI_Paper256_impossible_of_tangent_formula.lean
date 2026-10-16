-- Prove2me | Theorems.Thm_OAI_Paper256_impossible_of_tangent_formula
-- name    : OAI.Paper256.impossible_of_tangent_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:50:57.001499+00:00
-- url     : https://prove2.me/theorems/546c67a5-0bb6-40de-aec2-ea788ecce772
-- title:
--   No normalized pencil satisfies the Choi–Lam tangent formula
-- statement:
--   Throughout, $\mathrm{Sym}_n$ is the space of real symmetric $n\times n$ matrices, $I$ (or $I_n$) is the identity matrix, $M\succeq 0$ (resp. $M\succ 0$) means that $M$ is positive semidefinite (resp. positive definite), and $\|M\|$ is the spectral norm of a real, possibly rectangular, matrix, i.e. its operator norm as a linear map between Euclidean spaces.
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
--   For a square matrix $M$, $\Pi_{\ker M}$ denotes the matrix of the orthogonal projection of Euclidean space onto $\ker M$. For a unit vector $w\in\mathbb{R}^4$ put
--   $\Pi^D_w=\Pi_{\ker D(I_4-ww^{\top})}\in\mathbb{R}^{a\times a}$ and $\Pi^E_w=\Pi_{\ker E(I_4-ww^{\top})}\in\mathbb{R}^{c\times c}$.
--
--   The Choi–Lam biquadratic form on $\mathbb{R}^3\times\mathbb{R}^3$ is (indices modulo $3$)
--   $$
--   \Lambda(z,y)=\sum_{i=0}^{2}z_i^2y_i^2-2\bigl(z_0y_0z_1y_1+z_0y_0z_2y_2+z_1y_1z_2y_2\bigr)+\sum_{i=0}^{2}z_i^2y_{i+1}^2 ,
--   $$
--   and for $v=(v_0,v_1,v_2,v_3)$ and $u=(u_0,u_1,u_2,u_3)$ in $\mathbb{R}^4$ we write $w(v,u)\in\mathbb{R}^3$ for the vector with coordinates $w(v,u)_i=v_0u_{i+1}-u_0v_{i+1}$ for $i=0,1,2$.
--
--   **Statement.** Let $P=(a,c,D,E,B)$ be a normalized pencil, let $v\in\mathbb{R}^4$ be a unit vector with $v_0\neq0$, and let $T:\mathbb{R}^4\to\mathbb{R}^{c\times c}$ be a linear map. Then it is impossible that
--   $$
--   \Lambda\bigl(w(v,h),\,y\bigr)=\bigl\|\Pi^D_v\,B(y)\,T(h)\bigr\|^2\qquad\text{for all } h\in\mathbb{R}^4 \text{ with } \langle v,h\rangle=0 \text{ and all } y\in\mathbb{R}^3 .
--   $$
--   In other words, the assumption that this identity holds leads to a contradiction.
--
--   Together with the tangent identity, which produces exactly such $v$ and $T$ from any normalized pencil, this shows that no normalized pencil exists; this is the final step in proving that the hyperbolicity cone under study has no spectrahedral representation. The underlying phenomenon is a rigidity property of the Choi–Lam form: it cannot be written as the squared norm of a matrix-valued bilinear map.
--
--   **Formalization Note** The conclusion of the Lean theorem is `False`, with the identity as a hypothesis. $\langle v,h\rangle$ is `inner ℝ v h`, `operatorNorm` is the spectral norm, `P.leftProjection v` is $\Pi^D_v$, `wedgeCoordinates` is $w$ and `choiLam` is $\Lambda$. `NormalizedPencil` packages $(a,c,D,E,B)$ together with the positivity, unitality and Schur-equivalence fields; `phi y M` is $\varphi_y(M)$ and `qMatrix y` is $Q(y)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/TangentRigidity.lean#L14-L45

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
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

theorem OAI.Paper256.impossible_of_tangent_formula (P : NormalizedPencil)
    (v : Vec 4) (T : Vec 4 →ₗ[ℝ] Mat P.c ℝ)
    (hv : ‖v‖ = 1) (hv0 : v 0 ≠ 0)
    (hformula : ∀ h : Vec 4, inner ℝ v h = 0 → ∀ y : Fin 3 → ℝ,
      choiLam (wedgeCoordinates v h) y =
        operatorNorm (P.leftProjection v * P.B y * T h) ^ 2) : False := by sorry
