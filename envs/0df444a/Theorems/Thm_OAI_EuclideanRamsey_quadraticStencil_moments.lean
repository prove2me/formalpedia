-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_quadraticStencil_moments
-- name    : OAI.EuclideanRamsey.quadraticStencil_moments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:05:10.03743+00:00
-- url     : https://prove2.me/theorems/30a0a368-2823-4cd8-a6f2-5747c3f02fbb
-- title:
--   Mass and moments of the quadratic stencil $\tfrac12\sum_{a,b}C_{ab}\,\ell_a\ell_b$ in the group algebra $\mathbb{Q}[\mathbb{Z}^k]$
-- statement:
--   Let $k\in\mathbb{N}$ and let $\mathbb{Q}[\mathbb{Z}^k]$ be the group algebra of the lattice $\mathbb{Z}^k$ over $\mathbb{Q}$: its elements are finitely supported functions $\nu:\mathbb{Z}^k\to\mathbb{Q}$, written $\nu=\sum_\gamma\nu(\gamma)[\gamma]$, and the product is convolution, determined by $[\gamma][\delta]=[\gamma+\delta]$. For $\nu\in\mathbb{Q}[\mathbb{Z}^k]$ and indices $a,b\in\{1,\dots,k\}$ define the mass and the first and second moments
--   $$
--   m(\nu)=\sum_{\gamma}\nu(\gamma),\qquad M_1(\nu)_a=\sum_{\gamma}\nu(\gamma)\,\gamma_a,\qquad M_2(\nu)_{ab}=\sum_{\gamma}\nu(\gamma)\,\gamma_a\gamma_b .
--   $$
--   For a rational $k\times k$ matrix $C$ and elements $\ell_1,\dots,\ell_k\in\mathbb{Q}[\mathbb{Z}^k]$, the quadratic stencil is $Q_C(\ell)=\tfrac12\sum_{a,b=1}^kC_{ab}\,\ell_a\ell_b\in\mathbb{Q}[\mathbb{Z}^k]$.
--
--   **Theorem.** Let $C$ be symmetric, and suppose that $m(\ell_a)=0$ and $M_1(\ell_a)_b=\delta_{ab}$ (Kronecker delta) for all $a,b$. Then
--
--   $$
--   m\big(Q_C(\ell)\big)=0,\qquad M_1\big(Q_C(\ell)\big)_a=0,\qquad M_2\big(Q_C(\ell)\big)_{ab}=C_{ab}\qquad\text{for all }a,b .
--   $$
--
--   Elements $\ell_a$ with zero mass and first moments $\delta_{ab}$ behave to first order like the coordinate functions; the simplest example is $\ell_a=[\mathbf e_a]-[0]$. The theorem shows that the quadratic expression $Q_C(\ell)$ is then a rational lattice measure with vanishing mass and first moments and with second-moment matrix exactly $C$, a discrete analogue of the operator $\tfrac12\sum_{a,b}C_{ab}\partial_a\partial_b$. It is used to produce lattice measures with prescribed second moments in the algebraic part of the classification of Euclidean Ramsey configurations.
--
--   **Formalization Note** $\mathbb{Q}[\mathbb{Z}^k]$ is `LatticeRing k = AddMonoidAlgebra ℚ (Fin k → ℤ)`; $m$, $M_1$, $M_2$ are `mass`, `firstMoment` and `secondMoment`, defined by summing over the finite support of the coefficient function; $Q_C(\ell)$ is `quadraticStencil C l`, and symmetry is `C.IsSymm`. Indices range over `Fin k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/LatticeMoments.lean#L245-L262

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments

open OAI OAI.EuclideanRamsey
universe uIndex
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
variable {k : ℕ}

theorem OAI.EuclideanRamsey.quadraticStencil_moments (C : Matrix (Fin k) (Fin k) ℚ) (hC : C.IsSymm)
    (l : Fin k → LatticeRing k) (hm : ∀ a, mass (l a) = 0)
    (hf : ∀ a b, firstMoment (l a) b = if a = b then 1 else 0) :
    mass (quadraticStencil C l) = 0 ∧ (∀ a, firstMoment (quadraticStencil C l) a = 0) ∧
      (∀ a b, secondMoment (quadraticStencil C l) a b = C a b) := by sorry
