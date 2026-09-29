-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_sparse_concave_minimizer
-- name    : HlawkaSchatten.DiagonalConstruction.exists_sparse_concave_minimizer
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:50:07.229795+00:00
-- url     : https://prove2.me/theorems/2896e1af-050c-412d-ac39-97262922411c
-- title:
--   A sparse minimizer for a concave objective under three linear moments
-- statement:
--   Let $\iota$ be a finite index set. Fix nonnegative coefficients $A:\iota\to(\mathrm{Fin}\,3\to\mathbb{R})$, thought of as three linear functionals of a weight vector, such that each row sum $\sum_kA_{i,k}$ is strictly positive, and a target vector $b:\mathrm{Fin}\,3\to\mathbb{R}$ of three prescribed moments. Define the moment fiber
--   $$
--   \mathrm{momentFiber}(A,b) \;=\; \Big\{\, w:\iota\to\mathbb{R} \ \Big|\ \forall i,\ w_i\ge0,\ \text{and}\ \forall k,\ \sum_{i\in\iota} w_i A_{i,k} = b_k \,\Big\}
--   $$
--   of nonnegative weight vectors realizing exactly the moments $b$. Let $F:(\iota\to\mathbb{R})\to\mathbb{R}$ be continuous, and concave on the nonnegative-weight set $\{w:\forall i,\ w_i\ge0\}$.
--
--   Given a point $w_0$ already in the moment fiber, this theorem produces a point $w$, also in the moment fiber, such that:
--
--   1. $F(w)\le F(w_0)$, and
--   2. $w$ is supported on at most three coordinates, $\big|\{\,i\in\iota : w_i\ne0\,\}\big|\le3$.
--
--   This is the abstract sparsification result underlying the reduction of the diagonal construction to three coordinates. It is later instantiated with $A$ built from the three pairwise power sums $|x_i+y_i|^p,|x_i+z_i|^p,|y_i+z_i|^p$ and $F$ a weighted combination of weighted $p$-norms, reducing a purported failure of the Hlawka bound to at most three active coordinates.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Sparsification.lean#L59-L168

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Sparsification
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Three constraints admit a sparse concave minimizer

For nonnegative coordinate weights, fixing three positive linear moments
gives a compact feasible set. Minimize the concave objective, then maximize
the sum of squared weights among its minimizers. A supported kernel
direction would produce two feasible perturbations whose average squared
size is strictly larger. Thus at most three weights are positive.
-/


variable {ι : Type*} [Fintype ι]

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.exists_sparse_concave_minimizer
    (A : ι → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (hA : ∀ i k, 0 ≤ A i k) (hpos : ∀ i, 0 < ∑ k, A i k)
    (F : (ι → ℝ) → ℝ) (hF : Continuous F)
    (hconc : ConcaveOn ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} F)
    (w₀ : ι → ℝ) (hw₀ : w₀ ∈ momentFiber A b) :
    ∃ w ∈ momentFiber A b, F w ≤ F w₀ ∧ Fintype.card {i // w i ≠ 0} ≤ 3 := by sorry
