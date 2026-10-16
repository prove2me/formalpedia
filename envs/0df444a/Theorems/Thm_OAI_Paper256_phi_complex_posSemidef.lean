-- Prove2me | Theorems.Thm_OAI_Paper256_phi_complex_posSemidef
-- name    : OAI.Paper256.phi_complex_posSemidef
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:21:50.204981+00:00
-- url     : https://prove2.me/theorems/10464871-f24c-4efc-a3b2-522948a53960
-- title:
--   The map $\varphi_y$ preserves positive semidefiniteness of complex $4\times4$ matrices
-- statement:
--   For $y=(y_1,y_2,y_3)\in\mathbb{R}^3$ let $Q(y)$ be the symmetric $3\times3$ matrix
--   $$
--   Q(y)=\begin{pmatrix} y_1^2+y_2^2 & -y_1y_2 & -y_1y_3\\ -y_1y_2 & y_2^2+y_3^2 & -y_2y_3\\ -y_1y_3 & -y_2y_3 & y_3^2+y_1^2\end{pmatrix},
--   $$
--   and for a complex $4\times4$ matrix $M$ with rows and columns indexed by $0,1,2,3$, written in block form $M=\begin{pmatrix} m_{00} & a^{\mathsf T}\\ b & M'\end{pmatrix}$ ($m_{00}$ a scalar, $a,b$ column vectors of length $3$, $M'$ the lower right $3\times3$ block), put
--   $$
--   \varphi_y(M)=\begin{pmatrix}\operatorname{tr}\big(Q(y)M'\big) & -a^{\mathsf T}Q(y)\\ -Q(y)\,b & m_{00}\,Q(y)\end{pmatrix}.
--   $$
--
--   **Theorem.** For every real vector $y\in\mathbb{R}^3$ and every positive semidefinite matrix $X\in\mathbb{C}^{4\times4}$, the matrix $\varphi_y(X)$ is positive semidefinite:
--   $$
--   X\succeq 0\quad\Longrightarrow\quad \varphi_y(X)\succeq 0 .
--   $$
--   Here $M\succeq 0$ means that $M$ is Hermitian and $u^*Mu\ge 0$ for every $u\in\mathbb{C}^4$.
--
--   Thus, for each real parameter $y$, $\varphi_y$ is a positive linear map on $\mathbb{C}^{4\times4}$ (and it also commutes with taking adjoints). The quadratic form of $Q(y)$ is the Choi–Lam biquadratic form, and complex positivity of $\varphi_y$ is the input needed for resolvent-type invertibility arguments, in particular for showing that the polynomial $\det\big(\det(X)Z-\varphi_y(\operatorname{adj}X)\big)$ in the entries of symmetric $4\times4$ matrices $X,Z$ and of $y$ is hyperbolic: its restrictions to lines in the direction $(I,I,0)$ have only real roots.
--
--   **Formalization Note** In Lean the map is `phi` evaluated at the complexified parameter `fun i => (y i : ℂ)`; `qMatrix` uses indices in `Fin 3` read cyclically ($Q_{ii}=y_i^2+y_{i+1}^2$, $Q_{ij}=-y_iy_j$ for $i\ne j$). Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which includes the Hermitian condition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/ComplexPositive.lean#L81-L94

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
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix
universe u

theorem OAI.Paper256.phi_complex_posSemidef (y : Fin 3 → ℝ) (X : Mat 4 ℂ) (hX : X.PosSemidef) :
    (phi (fun i => (y i : ℂ)) X).PosSemidef := by sorry
