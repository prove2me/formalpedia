-- Prove2me | Theorems.Thm_OAI_Paper256_polynomial_homogeneous
-- name    : OAI.Paper256.polynomial_homogeneous
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:24:05.731221+00:00
-- url     : https://prove2.me/theorems/9c3a801d-e8d8-4dfe-a5ca-c4d4f36475e0
-- title:
--   The determinantal polynomial $\det\big(\det(X)Z-\varphi_y(\operatorname{adj}X)\big)$ is homogeneous of degree $20$
-- statement:
--   Work in the real polynomial ring in $23$ variables $x_{ij}$, $z_{ij}$ ($0\le i\le j\le3$, ten of each) and $y_1,y_2,y_3$. Let $X$ and $Z$ be the symmetric $4\times4$ matrices of variables, $X_{ij}=X_{ji}=x_{ij}$ and $Z_{ij}=Z_{ji}=z_{ij}$ for $i\le j$, and let $y=(y_1,y_2,y_3)$. Let $Q(y)$ be the symmetric $3\times3$ matrix
--   $$
--   Q(y)=\begin{pmatrix} y_1^2+y_2^2 & -y_1y_2 & -y_1y_3\\ -y_1y_2 & y_2^2+y_3^2 & -y_2y_3\\ -y_1y_3 & -y_2y_3 & y_3^2+y_1^2\end{pmatrix},
--   $$
--   and for a $4\times4$ matrix $M$ with polynomial entries, rows and columns indexed by $0,1,2,3$, written in block form $M=\begin{pmatrix} m_{00} & a^{\mathsf T}\\ b & M'\end{pmatrix}$ ($m_{00}$ a scalar, $a,b$ column vectors of length $3$, $M'$ the lower right $3\times3$ block), put
--   $$
--   \varphi_y(M)=\begin{pmatrix}\operatorname{tr}\big(Q(y)M'\big) & -a^{\mathsf T}Q(y)\\ -Q(y)\,b & m_{00}\,Q(y)\end{pmatrix}.
--   $$
--   Define
--   $$
--   p=\det\big(\det(X)\,Z-\varphi_y(\operatorname{adj}X)\big),
--   $$
--   where $\operatorname{adj}X$ is the adjugate (classical adjoint) of $X$.
--
--   **Theorem.** $p$ is a homogeneous polynomial of degree $20$: every monomial occurring in $p$ with a nonzero coefficient has total degree exactly $20$.
--
--   Homogeneity is one of the defining features of a hyperbolic polynomial. It implies $p(sx)=s^{20}p(x)$ for all real $s$ and all points $x$, in particular $p(-x)=p(x)$, which is used to translate statements about the roots of $t\mapsto p(te-x)$ into statements about the shifted points $x+te$.
--
--   **Formalization Note** The statement is `MvPolynomial.IsHomogeneous polynomial 20`. This predicate alone does not assert that $p\neq0$ (the zero polynomial is homogeneous of every degree). The variables are indexed by `Coord`, i.e. two copies of the upper-triangular index set $\{(i,j):i\le j\}$ of `Fin 4` together with `Fin 3`; indices start at $0$, and `qMatrix` is written cyclically as $Q_{ii}=y_i^2+y_{i+1}^2$, $Q_{ij}=-y_iy_j$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PolynomialHomogeneous.lean#L77-L103

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

open OAI OAI.Paper256
open Matrix MvPolynomial
open scoped BigOperators
universe u v

theorem OAI.Paper256.polynomial_homogeneous : polynomial.IsHomogeneous 20 := by sorry
