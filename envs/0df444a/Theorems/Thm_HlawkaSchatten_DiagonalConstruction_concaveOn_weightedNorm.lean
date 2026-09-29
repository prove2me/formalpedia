-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_concaveOn_weightedNorm
-- name    : HlawkaSchatten.DiagonalConstruction.concaveOn_weightedNorm
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:48:12.557787+00:00
-- url     : https://prove2.me/theorems/c0388408-6ee8-428d-a0d7-f98fbf02da54
-- title:
--   Concavity of the weighted $p$-norm in its weights
-- statement:
--   Let $\iota$ be a finite index set, $p>1$, and $x:\iota\to\mathbb{R}$ a fixed real vector. For a weight vector $w:\iota\to\mathbb{R}$ with every $w_i\ge0$, define the weighted norm
--   $$
--   \mathrm{weightedNorm}_p(x,w) \;=\; \Big(\sum_{i\in\iota} w_i\,|x_i|^{p}\Big)^{1/p}.
--   $$
--
--   Then, with $x$ fixed, the map $w\mapsto \mathrm{weightedNorm}_p(x,w)$ is concave on the convex set $\{w:\iota\to\mathbb{R} : \forall i,\ w_i\ge0\}$ of nonnegative weight vectors.
--
--   This concavity in the reweighting variable $w$ — rather than in $x$ — is the key convexity-analytic fact behind the three-coordinate reduction of the sharp diagonal construction. It lets a linear combination of such weighted norms, built from $x$, $y$, $z$, and $x+y+z$, be treated as a single concave objective on the space of nonnegative coordinate weights, so its minimizers can be analyzed by a sparse-minimizer argument rather than by direct case analysis on the ambient index set $\iota$. Combining several such weighted norms this way — by summing them, or by a common nonnegative scalar multiple — again yields a concave function only because the combining coefficients are nonnegative; a negative coefficient would flip a concave summand to convex.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/WeightedCoordinates.lean#L54-L67

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_WeightedCoordinates
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Concavity under common coordinate reweighting -/


variable {ι : Type*} [Fintype ι]

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.concaveOn_weightedNorm {p : ℝ} (hp : 1 < p) (x : ι → ℝ) :
    ConcaveOn ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} (weightedNorm p x) := by sorry
