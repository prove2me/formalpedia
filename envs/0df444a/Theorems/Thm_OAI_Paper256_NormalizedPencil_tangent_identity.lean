-- Prove2me | Theorems.Thm_OAI_Paper256_NormalizedPencil_tangent_identity
-- name    : OAI.Paper256.NormalizedPencil.tangent_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:50:05.922629+00:00
-- url     : https://prove2.me/theorems/9c054a60-3751-493d-aeb1-40aa3140ce8b
-- title:
--   Tangent identity: differentiating the rank-one norm identity along the sphere
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
--   **Statement.** For every normalized pencil $P=(a,c,D,E,B)$ there exist a unit vector $v\in\mathbb{R}^4$ with $v_0\neq 0$ and a linear map $T:\mathbb{R}^4\to\mathbb{R}^{c\times c}$ such that for every $h\in\mathbb{R}^4$ with $\langle v,h\rangle=0$ and every $y\in\mathbb{R}^3$,
--   $$
--   \Lambda\bigl(w(v,h),\,y\bigr)=\bigl\|\Pi^D_v\,B(y)\,T(h)\bigr\|^2 .
--   $$
--
--   In the rank-one norm identity $\Lambda(w(v,u),y)=\|\Pi^D_vB(y)\Pi^E_u\|^2$ the projection $\Pi^E_u$ depends non-linearly on $u$. The tangent identity replaces it by its derivative $T(h)$ in the tangent direction $h$, so that the matrix inside the norm becomes bilinear in $(h,y)$. This linearized form is exactly what is refuted by the rigidity of the Choi–Lam form, showing that normalized pencils cannot exist.
--
--   **Formalization Note** $T$ is a `LinearMap` from `EuclideanSpace ℝ (Fin 4)` to $c\times c$ real matrices, defined on all of $\mathbb{R}^4$ although the identity is asserted only for $h$ orthogonal to $v$; $\langle v,h\rangle$ is the Euclidean inner product `inner ℝ v h`, and $v_0$ is the coordinate of index $0$. `operatorNorm` is the spectral norm, `P.leftProjection v` is $\Pi^D_v$, `wedgeCoordinates` is $w$ and `choiLam` is $\Lambda$. `NormalizedPencil` packages $(a,c,D,E,B)$ together with the positivity, unitality and Schur-equivalence fields; `phi y M` is $\varphi_y(M)$ and `qMatrix y` is $Q(y)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/TangentIdentity.lean#L15-L44

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

theorem OAI.Paper256.NormalizedPencil.tangent_identity (P : NormalizedPencil) :
    ∃ (v : Vec 4) (T : Vec 4 →ₗ[ℝ] Mat P.c ℝ),
      ‖v‖ = 1 ∧ v 0 ≠ 0 ∧ ∀ h : Vec 4, inner ℝ v h = 0 → ∀ y : Fin 3 → ℝ,
        choiLam (wedgeCoordinates v h) y =
          operatorNorm (P.leftProjection v * P.B y * T h) ^ 2 := by sorry
