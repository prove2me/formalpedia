-- Prove2me | Theorems.Thm_OAI_Paper256_basePoint_mem_interior_cone
-- name    : OAI.Paper256.basePoint_mem_interior_cone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:33:14.756518+00:00
-- url     : https://prove2.me/theorems/e4afe532-eee9-47e2-94d7-6b6869b397ba
-- title:
--   The base point $(I,I,0)$ lies in the interior of the hyperbolicity cone
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
--   **Theorem.** The point $e$ is an interior point of $\Lambda$ (for the usual topology of the finite-dimensional real vector space $V$):
--   $$
--   e=(I_4,I_4,0)\in\operatorname{int}\Lambda .
--   $$
--
--   This is the basic nondegeneracy property of a hyperbolicity cone: the hyperbolic direction $e$ lies in the interior of the cone, so in particular $\Lambda$ has nonempty interior. It is used when $\Lambda$ is compared with the feasible set of a linear matrix inequality.
--
--   **Formalization Note** In Lean, $V$ is `Ambient`, $p$ is `polynomial` (an `MvPolynomial` whose variables are indexed by `Coord`: two copies of the upper-triangular index set $\{(i,j):i\le j\}$ together with `Fin 3`), $e$ is `basePoint`, $p_x$ is `linePolynomial x` (obtained by substituting $t\,e_i-x_i$ for every coordinate), and $\Lambda$ is `cone`; complex roots are taken with `Polynomial.aeval`. Indices in `Fin 3` and `Fin 4` start at $0$, and `qMatrix` is written cyclically as $Q_{ii}=y_i^2+y_{i+1}^2$, $Q_{ij}=-y_iy_j$. The topology on `Ambient` is the product of the subspace topologies on `Sym 4` and the product topology on `Fin 3 → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/ConeInterior.lean#L13-L43

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
open scoped Topology Matrix.Norms.L2Operator

theorem OAI.Paper256.basePoint_mem_interior_cone : basePoint ∈ interior cone := by sorry
