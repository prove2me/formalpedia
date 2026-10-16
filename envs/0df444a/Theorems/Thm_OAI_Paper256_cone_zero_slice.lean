-- Prove2me | Theorems.Thm_OAI_Paper256_cone_zero_slice
-- name    : OAI.Paper256.cone_zero_slice
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:36:58.931322+00:00
-- url     : https://prove2.me/theorems/aba2bfb8-36bb-49fd-9c63-517de555c01b
-- title:
--   The $y=0$ slice of the hyperbolicity cone is a product of two positive semidefinite cones
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
--   **Theorem.** For all $X,Z\in\mathrm{Sym}_4$,
--   $$
--   (X,Z,0)\in\Lambda\quad\Longleftrightarrow\quad X\succeq0\ \text{ and }\ Z\succeq0,
--   $$
--   where $M\succeq0$ means that the symmetric matrix $M$ is positive semidefinite.
--
--   Thus the intersection of $\Lambda$ with the subspace $\{y=0\}$ is the product of two copies of the cone of positive semidefinite $4\times4$ matrices. This identification is used when normalizing a hypothetical linear matrix inequality description of $\Lambda$.
--
--   **Formalization Note** In Lean, $V$ is `Ambient`, $p$ is `polynomial` (an `MvPolynomial` whose variables are indexed by `Coord`: two copies of the upper-triangular index set $\{(i,j):i\le j\}$ together with `Fin 3`), $e$ is `basePoint`, $p_x$ is `linePolynomial x` (obtained by substituting $t\,e_i-x_i$ for every coordinate), and $\Lambda$ is `cone`; complex roots are taken with `Polynomial.aeval`. Indices in `Fin 3` and `Fin 4` start at $0$, and `qMatrix` is written cyclically as $Q_{ii}=y_i^2+y_{i+1}^2$, $Q_{ij}=-y_iy_j$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/ConeZero.lean#L31-L49

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
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

theorem OAI.Paper256.cone_zero_slice (X Z : Sym 4) : ((X, Z), (0 : Fin 3 → ℝ)) ∈ cone ↔
    (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef := by sorry
