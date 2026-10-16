-- Prove2me | Theorems.Thm_OAI_Paper256_NormalizedPencil_norm_identity
-- name    : OAI.Paper256.NormalizedPencil.norm_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:49:29.525439+00:00
-- url     : https://prove2.me/theorems/f3fe1488-5802-4077-8a27-9b963d55cc85
-- title:
--   Rank-one norm identity linking the Choi–Lam form to a normalized pencil
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
--   **Statement.** Let $P=(a,c,D,E,B)$ be a normalized pencil, let $u,v\in\mathbb{R}^4$ be unit vectors ($\|u\|=\|v\|=1$ for the Euclidean norm) and let $y\in\mathbb{R}^3$. Then
--   $$
--   \Lambda\bigl(w(v,u),\,y\bigr)=\bigl\|\Pi^D_v\,B(y)\,\Pi^E_u\bigr\|^2 .
--   $$
--
--   The left side is an explicit polynomial (the Choi–Lam form), while the right side is built from an arbitrary normalized pencil; this identity is the bridge between the two. It is later differentiated in $u$ along the unit sphere, and the resulting tangent identity is shown to be impossible, which rules out normalized pencils. As a special case, $u=v$ gives $w(v,v)=0$ and hence $\Pi^D_v B(y)\Pi^E_v=0$.
--
--   **Formalization Note** `operatorNorm M` is the operator norm of the linear map between Euclidean spaces induced by $M$ (the spectral norm); `P.leftProjection v` and `P.rightProjection u` are $\Pi^D_v$ and $\Pi^E_u$, built with `kernelProjection`; `wedgeCoordinates v u` is $w(v,u)$ and `choiLam` is $\Lambda$. Vectors in $\mathbb{R}^4$ are elements of `EuclideanSpace ℝ (Fin 4)` with coordinates indexed by $0,1,2,3$. `NormalizedPencil` packages $(a,c,D,E,B)$ together with the positivity, unitality and Schur-equivalence fields; `phi y M` is $\varphi_y(M)$ and `qMatrix y` is $Q(y)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/NormIdentity.lean#L16-L65

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
open Matrix Filter Topology

theorem OAI.Paper256.NormalizedPencil.norm_identity (P : NormalizedPencil)
    (u v : Vec 4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (y : Fin 3 → ℝ) :
    choiLam (wedgeCoordinates v u) y =
      operatorNorm (P.leftProjection v * P.B y * P.rightProjection u) ^ 2 := by sorry
