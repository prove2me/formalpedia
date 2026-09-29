-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_euclideanSq_apply_lower
-- name    : HlawkaSchatten.DiagonalConstruction.euclideanSq_apply_lower
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:02:40.581439+00:00
-- url     : https://prove2.me/theorems/0a6b84c3-806b-4079-85dc-afc7c95da41b
-- title:
--   A uniform lower bound for the cyclic box's column-combination map
-- statement:
--   For a *triple* $X$ — three columns $X_0, X_1, X_2 \in \mathbb{R}^3$, with $X_{j,i}$ denoting coordinate $i$ of column $j$ (Lean: `X j i`) — write
--   $$\lVert a \rVert_2^2 := \sum_i a_i^2$$
--   for the squared Euclidean norm of $a \in \mathbb{R}^3$, and let
--   $$(\mathrm{applyTriple}\,X\,a)_i := \sum_j a_j\,X_{j,i}$$
--   be the linear combination $a_0X_0+a_1X_1+a_2X_2$ of the three columns of $X$ with weights $a$, read coordinatewise. Let $\mathrm{cyclicCenter}$ be the triple whose $j$-th column has $-1$ in position $j$ and $1$ in the other two positions (columns $(-1,1,1)$, $(1,-1,1)$, $(1,1,-1)$), and let
--   $$\mathrm{entryBox} := \{X : |X_{j,i} - \mathrm{cyclicCenter}_{j,i}| \le 19/100 \text{ for all } j, i\}.$$
--
--   For every $X \in \mathrm{entryBox}$ and every $a \in \mathbb{R}^3$,
--   $$\left(\frac{43}{100}\right)^2 \lVert a \rVert_2^2 \;\le\; \lVert \mathrm{applyTriple}\,X\,a \rVert_2^2.$$
--
--   Equivalently, the Euclidean norm of $\mathrm{applyTriple}\,X\,a$ is at least $43/100$ times the Euclidean norm of $a$.
--
--   This is a uniform bound on how much the linear map $a \mapsto \mathrm{applyTriple}\,X\,a$ can shrink lengths, valid simultaneously for every $X$ in the box: whichever such $X$ is used, applying it to any weight vector $a$ never produces an output shorter than $43/100$ of $a$'s own length. The bound is what lets a later estimate recover the size of a perturbation to $X$ from the sizes of simpler, per-column pieces.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/BoxGeometry.lean#L93-L112

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Quadratic geometry of the cyclic box

The joint radial estimate uses the convenient bound `300`. This weaker
intermediate constant leaves the exponent cutoff unchanged.
-/

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.euclideanSq_apply_lower {X : Triple} (hX : X ∈ entryBox) (a : Fin 3 → ℝ) :
    (43 / 100 : ℝ) ^ 2 * euclideanSq a ≤ euclideanSq (applyTriple X a) := by sorry
