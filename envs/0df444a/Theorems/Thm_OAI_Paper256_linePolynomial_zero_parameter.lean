-- Prove2me | Theorems.Thm_OAI_Paper256_linePolynomial_zero_parameter
-- name    : OAI.Paper256.linePolynomial_zero_parameter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:33:43.561184+00:00
-- url     : https://prove2.me/theorems/939ae19e-123d-45f1-bc65-0daf657da4bb
-- title:
--   On the slice $y=0$ the line polynomial factors as $\chi_X^4\,\chi_Z$
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
--   For a real square matrix $M$ let $\chi_M(t)=\det(tI-M)$ be its (monic) characteristic polynomial.
--
--   **Theorem.** For all $X,Z\in\mathrm{Sym}_4$, the line polynomial of the point $(X,Z,0)$ satisfies, as an identity in $\mathbb{R}[t]$,
--   $$
--   p_{(X,Z,0)}(t)=\chi_X(t)^4\,\chi_Z(t).
--   $$
--
--   On the slice $y=0$ the map $\varphi_0$ vanishes, and the polynomial decouples into characteristic polynomials. In particular, the roots of $p_{(X,Z,0)}$ are exactly the eigenvalues of $X$ and of $Z$. This is the basis for identifying the $y=0$ slice of the cone $\{x\in V:\ \text{all roots of } p_x \text{ are real and nonnegative}\}$ with the pairs of positive semidefinite matrices.
--
--   **Formalization Note** In Lean, $p_x$ is `linePolynomial x`, obtained by substituting $t\,e_i-x_i$ for the $23$ coordinates of the multivariate polynomial `polynomial`, with $e=(I,I,0)$ = `basePoint`; $\chi_M$ is Mathlib's `Matrix.charpoly`, which is $\det(tI-M)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/ZeroPolynomial.lean#L20-L36

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
open scoped Matrix.Norms.L2Operator
universe u

theorem OAI.Paper256.linePolynomial_zero_parameter (X Z : Sym 4) :
    linePolynomial ((X, Z), (0 : Fin 3 → ℝ)) =
      (X : Mat 4 ℝ).charpoly ^ 4 * (Z : Mat 4 ℝ).charpoly := by sorry
