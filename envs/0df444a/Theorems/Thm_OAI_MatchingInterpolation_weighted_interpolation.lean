-- Prove2me | Theorems.Thm_OAI_MatchingInterpolation_weighted_interpolation
-- name    : OAI.MatchingInterpolation.weighted_interpolation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:21:13.131058+00:00
-- url     : https://prove2.me/theorems/7a41b52e-fac6-4a30-bd86-0f18f4ae8b48
-- title:
--   Five-point second difference of a low-degree polynomial as a weighted sum over a dilated grid
-- statement:
--   Let $d\in\mathbb{N}$ and write points of $\mathbb{R}^3$ as $x=(x_0,x_1,x_2)$. $\mathcal P_d$ denotes the real vector space of functions $\mathbb{R}^3\to\mathbb{R}$ spanned by all products of at most $d$ coordinate functions $x\mapsto x_a$, $a\in\{0,1,2\}$ (repetitions allowed, the empty product being the constant $1$); these are exactly the polynomial functions of total degree at most $d$ in three variables. For $k\in\{0,\dots,d\}$ let $\ell_k(t)=\prod_{j\in\{0,\dots,d\},\,j\neq k}\frac{t-j}{k-j}$ be the Lagrange basis polynomial of the nodes $0,1,\dots,d$, and for a grid index $g=(g_0,g_1,g_2)\in\{0,\dots,d\}^3$ and a vector $v\in\mathbb{R}^3$ let $\Lambda_{g,v}(t)=\prod_{a=0}^{2}\ell_{g_a}(v_a t)$, a polynomial in one variable $t$.
--
--   Fix the base point $o=(1,0,0)$ and the directions $\alpha=(0,2,0)$, $\beta=(0,0,2)$, $\sigma=(2,0,0)$, $\pi=(-1,1,1)$. The weight polynomial of $g$ and the interpolation weights are
--   $$\Omega_g=\Lambda_{g,\alpha}+\Lambda_{g,\beta}-\Lambda_{g,\sigma}-2\Lambda_{g,\pi}+\Lambda_{g,0},\qquad w_{d,L}(g)=\Omega_g(1/L).$$
--
--   **Theorem.** For every $P\in\mathcal P_d$ and every real $L\neq0$,
--   $$P(o+\alpha)+P(o+\beta)-P(o+\sigma)-2P(o+\pi)+P(o)=\sum_{g\in\{0,\dots,d\}^3}w_{d,L}(g)\,P(o+Lg).$$
--   The five points on the left are $o+\alpha=(1,2,0)$, $o+\beta=(1,0,2)$, $o+\sigma=(3,0,0)$, $o+\pi=(0,1,1)$ and $o=(1,0,0)$, while $o+Lg=(1+Lg_0,\,Lg_1,\,Lg_2)$ runs over a dilated copy of the grid $\{0,\dots,d\}^3$.
--
--   The weights do not depend on $P$, so the identity is a fixed quadrature-type rule: this five-point second-order difference of any polynomial of degree at most $d$ is a linear combination of its values on the grid $o+L\{0,\dots,d\}^3$, whose points lie far from the five special points when $L$ is large. A companion result bounds the weights by $|w_{d,L}(g)|\le c_d/L^2$ for $L\ge1$. Together they allow one to compare functions that are close to low-degree polynomials at the five special points with their values on the far grid; in the perfect matching argument this is done entrywise for matrix-valued functions.
--
--   **Formalization Note** The space $\mathcal P_d$ is `lowDegree coord d`, the span of products of lists of length at most $d$ of coordinate functions. The weights are `weight d L g`, defined by evaluating `weightPolynomial d g` at `L⁻¹`; since Lean's inverse satisfies $0^{-1}=0$, the hypothesis $L\neq0$ is stated explicitly. The points appear as `origin + dirA`, `origin + dirB`, `origin + dirStar`, `origin + dirP`, `origin`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PolynomialInterpolation.lean#L188-L208

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation

open OAI OAI.MatchingInterpolation
open Polynomial
open MatchingSmoothing

theorem OAI.MatchingInterpolation.weighted_interpolation (d : ℕ) (P : Point → ℝ) (hP : P ∈ lowDegree coord d)
    (L : ℝ) (hL : L ≠ 0) :
    P (origin + dirA) + P (origin + dirB) - P (origin + dirStar) -
      2 * P (origin + dirP) + P origin =
      ∑ g : GridIndex d, weight d L g * P (fun a => origin a + L*(g a:ℝ)) := by sorry
