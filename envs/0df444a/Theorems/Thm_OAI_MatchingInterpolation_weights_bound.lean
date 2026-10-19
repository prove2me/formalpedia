-- Prove2me | Theorems.Thm_OAI_MatchingInterpolation_weights_bound
-- name    : OAI.MatchingInterpolation.weights_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:20:27.827186+00:00
-- url     : https://prove2.me/theorems/e2fca3f1-2e3e-40e3-a26d-043043926ab5
-- title:
--   Second-difference interpolation weights on a scaled grid decay like $1/L^2$
-- statement:
--   Fix $d\in\mathbb{N}$. For $k\in\{0,\dots,d\}$ let $\ell_k$ be the Lagrange basis polynomial for the nodes $0,1,\dots,d$:
--   $$\ell_k(t)=\prod_{j\neq k}\frac{t-j}{k-j},\qquad\ell_k(j)=\delta_{jk}.$$
--   For a grid index $g=(g_0,g_1,g_2)\in\{0,\dots,d\}^3$ let $\tau_g(x)=\ell_{g_0}(x_0)\,\ell_{g_1}(x_1)\,\ell_{g_2}(x_2)$ for $x\in\mathbb{R}^3$. With the direction vectors $a=(0,2,0)$, $b=(0,0,2)$, $u=(2,0,0)$ and $p=(-1,1,1)$, define for real $L\ge1$ the *weight*
--   $$w_{d,L}(g)=\tau_g\!\left(\tfrac aL\right)+\tau_g\!\left(\tfrac bL\right)-\tau_g\!\left(\tfrac uL\right)-2\,\tau_g\!\left(\tfrac pL\right)+\tau_g(0).$$
--
--   **Theorem.** There is a constant $c>0$, depending only on $d$, such that for every real $L\ge1$ and every $g\in\{0,\dots,d\}^3$
--   $$|w_{d,L}(g)|\le\frac{c}{L^2}.$$
--
--   The weights express a second-order finite difference of a polynomial $P$ of degree at most $d$ at the base point $x_0=(1,0,0)$, namely
--   $$P(x_0+a)+P(x_0+b)-P(x_0+u)-2P(x_0+p)+P(x_0),$$
--   through the values of $P$ on the scaled grid $x_0+L\{0,\dots,d\}^3$. The bound says that all these weights are $O(L^{-2})$ uniformly in $g$. Small errors in the grid values therefore transfer to the finite difference with a damping factor $L^{-2}$, which drives the interpolation step of the PSD-rank lower bound for perfect matchings.
--
--   **Formalization Note** The Lagrange basis is `Lagrange.basis` on the real nodes $0,\dots,d$, grid indices are functions `Fin 3 → Fin (d+1)`, and `weight d L g` is defined as the value at $L^{-1}$ of the polynomial $t\mapsto\tau_g(ta)+\tau_g(tb)-\tau_g(tu)-2\tau_g(tp)+\tau_g(0)$ (`weightPolynomial d g`). For $L\ge1$ this is the displayed formula.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PolynomialInterpolation.lean#L146-L162

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

theorem OAI.MatchingInterpolation.weights_bound (d : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 1 ≤ L →
    ∀ g : GridIndex d, |weight d L g| ≤ c / L^2 := by sorry
