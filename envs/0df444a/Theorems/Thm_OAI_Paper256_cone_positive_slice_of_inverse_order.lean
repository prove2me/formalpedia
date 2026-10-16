-- Prove2me | Theorems.Thm_OAI_Paper256_cone_positive_slice_of_inverse_order
-- name    : OAI.Paper256.cone_positive_slice_of_inverse_order
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:31:26.147347+00:00
-- url     : https://prove2.me/theorems/22b15d36-4e16-4dd2-a835-c210d329ad53
-- title:
--   Over positive definite $X$, cone membership is the matrix inequality $Z-\varphi_y(X^{-1})\succeq0$
-- statement:
--   For $y=(y_1,y_2,y_3)\in\mathbb{R}^3$ let $Q(y)$ be the symmetric $3\times3$ matrix
--   $$
--   Q(y)=\begin{pmatrix} y_1^2+y_2^2 & -y_1y_2 & -y_1y_3\\ -y_1y_2 & y_2^2+y_3^2 & -y_2y_3\\ -y_1y_3 & -y_2y_3 & y_3^2+y_1^2\end{pmatrix},
--   $$
--   and for a $4\times4$ matrix $M$ with rows and columns indexed by $0,1,2,3$, written in block form $M=\begin{pmatrix} m_{00} & a^{\mathsf T}\\ b & M'\end{pmatrix}$ ($m_{00}$ a scalar, $a,b$ column vectors of length $3$, $M'$ the lower right $3\times3$ block), put
--   $$
--   \varphi_y(M)=\begin{pmatrix}\operatorname{tr}\big(Q(y)M'\big) & -a^{\mathsf T}Q(y)\\ -Q(y)\,b & m_{00}\,Q(y)\end{pmatrix}.
--   $$
--
--   Let $V=\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$, where $\mathrm{Sym}_4$ denotes the real symmetric $4\times4$ matrices; $V$ is a real vector space of dimension $10+10+3=23$. Define the polynomial function $p:V\to\mathbb{R}$ by
--   $$
--   p(X,Z,y)=\det\big(\det(X)\,Z-\varphi_y(\operatorname{adj}X)\big),
--   $$
--   where $\operatorname{adj}X$ is the adjugate of $X$; it is a polynomial in the $23$ coordinates of $V$ (the upper triangular entries of $X$ and of $Z$, and $y_1,y_2,y_3$). Let $e=(I_4,I_4,0)\in V$. For $x=(X,Z,y)\in V$ the line polynomial of $x$ is the real polynomial in one variable
--   $$
--   p_x(t)=p(te-x)=\det\big(\det(tI-X)\,(tI-Z)-\varphi_{-y}(\operatorname{adj}(tI-X))\big)
--   $$
--   (note that $\varphi_{-y}=\varphi_y$ because $Q(-y)=Q(y)$).
--
--   The cone $\Lambda\subseteq V$ is the set of points all of whose line-polynomial roots are real and nonnegative:
--   $$
--   \Lambda=\{x\in V:\ \text{every } t\in\mathbb{C} \text{ with } p_x(t)=0 \text{ satisfies } \operatorname{Im}t=0 \text{ and } \operatorname{Re}t\ge 0\}.
--   $$
--
--   **Theorem.** Let $X,Z\in\mathrm{Sym}_4$ and $y\in\mathbb{R}^3$. Assume that $X$ is positive definite and that
--   $$
--   X^{-1}-(X+tI)^{-1}\succeq0\qquad\text{for every } t\ge0 .
--   $$
--   Then
--   $$
--   (X,Z,y)\in\Lambda\quad\Longleftrightarrow\quad Z-\varphi_y(X^{-1})\succeq0 .
--   $$
--   Here $M\succeq0$ means that the symmetric matrix $M$ is positive semidefinite.
--
--   So, over the region where $X$ is positive definite, the cone $\Lambda$ is described by a Schur-complement-type linear matrix inequality in $Z$. The extra hypothesis is the operator antitonicity of matrix inversion; it holds for every positive definite $X$, so the description is valid for all positive definite $X$ once this standard fact is supplied.
--
--   **Formalization Note** The right-hand side is stated for `coneResidual X Z y 0`, where `coneResidual X Z y t` $=Z+tI-\varphi_y\big((X+tI)^{-1}\big)$; at $t=0$ this is $Z-\varphi_y(X^{-1})$. Matrix inverses are Mathlib's total `Matrix.inv`, which agrees with the usual inverse here because $X+tI$ is positive definite. In Lean, $V$ is `Ambient`, $p$ is `polynomial` (an `MvPolynomial` whose variables are indexed by `Coord`: two copies of the upper-triangular index set $\{(i,j):i\le j\}$ together with `Fin 3`), $e$ is `basePoint`, $p_x$ is `linePolynomial x` (obtained by substituting $t\,e_i-x_i$ for every coordinate), and $\Lambda$ is `cone`; complex roots are taken with `Polynomial.aeval`. Indices in `Fin 3` and `Fin 4` start at $0$, and `qMatrix` is written cyclically as $Q_{ii}=y_i^2+y_{i+1}^2$, $Q_{ij}=-y_iy_j$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PositiveCore.lean#L16-L37

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

open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

theorem OAI.Paper256.cone_positive_slice_of_inverse_order (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hX : (X : Mat 4 ℝ).PosDef)
    (hOrder : ∀ t : ℝ, 0 ≤ t →
      ((X : Mat 4 ℝ)⁻¹ - ((X + t • 1 : Sym 4) : Mat 4 ℝ)⁻¹).PosSemidef) :
    ((X, Z), y) ∈ cone ↔ (coneResidual X Z y 0 : Mat 4 ℝ).PosSemidef := by sorry
