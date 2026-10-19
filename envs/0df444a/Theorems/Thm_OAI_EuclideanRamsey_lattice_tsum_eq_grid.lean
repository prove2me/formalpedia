-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_lattice_tsum_eq_grid
-- name    : OAI.EuclideanRamsey.lattice_tsum_eq_grid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:07:33.61076+00:00
-- url     : https://prove2.me/theorems/b8029314-2ecb-4945-a18a-099fbbb7839e
-- title:
--   Lattice sums over $\mathbb{Z}^k$ as sums over the grid points $s\cap\tfrac1n\mathbb{Z}^k$
-- statement:
--   Let $k\in\mathbb{N}$ and let $n$ be a positive integer. For $\gamma\in\mathbb{Z}^k$ write $\gamma/n=(\gamma_1/n,\dots,\gamma_k/n)\in\mathbb{R}^k$, and let $\tfrac1n\mathbb{Z}^k=\{\gamma/n:\gamma\in\mathbb{Z}^k\}$ be the scaled integer lattice. Let $s\subseteq\mathbb{R}^k$ be any set and let $f:\mathbb{R}^k\to\mathbb{R}$ be a function whose support $\{x:f(x)\neq0\}$ is contained in $s$. Then
--
--   $$
--   \sum_{\gamma\in\mathbb{Z}^k}f(\gamma/n)\;=\;\sum_{x\in s\,\cap\,\frac1n\mathbb{Z}^k}f(x).
--   $$
--
--   Both sides are unconditional sums; no summability or finiteness assumption is needed (see the Formalization Note for the convention used when a family is not summable).
--
--   The identity converts a sum over lattice samples into a sum over the grid points of $s$, which is the form in which Riemann-sum and lattice-point-counting theorems are stated. When $s$ is bounded, the right side is a finite sum.
--
--   **Formalization Note** Both sums are `tsum`s, which equal the sum of the family when it is summable and $0$ otherwise; the identity holds in this sense in all cases. The point $\gamma/n$ is `latticeSample n γ`, and $\frac1n\mathbb{Z}^k$ is `(n:ℝ)⁻¹ • realLattice k`, where `realLattice k` is the $\mathbb{Z}$-span of the standard basis of `Fin k → ℝ`. The hypothesis on $n$ is `n ≠ 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean#L150-L166

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization

open OAI OAI.EuclideanRamsey
universe uDomain uIndex
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open MeasureTheory
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter

theorem OAI.EuclideanRamsey.lattice_tsum_eq_grid {k n : ℕ} (hn : n ≠ 0) (s : Set (Fin k → ℝ))
    (f : (Fin k → ℝ) → ℝ) (hf : Function.support f ⊆ s) :
    (∑' γ : Fin k → ℤ, f (latticeSample n γ)) =
      ∑' x : ↑(s ∩ (n:ℝ)⁻¹ • realLattice k), f x := by sorry
