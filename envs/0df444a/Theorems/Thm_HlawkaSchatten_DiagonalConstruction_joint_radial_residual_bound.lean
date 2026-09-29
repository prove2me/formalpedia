-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_joint_radial_residual_bound
-- name    : HlawkaSchatten.DiagonalConstruction.joint_radial_residual_bound
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:08:44.743398+00:00
-- url     : https://prove2.me/theorems/3d3e1d4d-43ef-4e14-8cd0-b043245efbda
-- title:
--   Bounding a joint radial residual by per-column and total residuals on the cyclic box
-- statement:
--   Write a *triple* as three columns $X_0,X_1,X_2\in\mathbb R^3$, with $X_{j,i}$ coordinate $i$ of column $j$ (Lean: `X j i`). For a triple $X$, let
--   $$\lVert X\rVert_F^2 := \sum_j \lVert X_j\rVert_2^2 = \sum_j\sum_i X_{j,i}^2$$
--   be its squared Frobenius norm (`frobeniusSq`), and let $\mathrm{totalTriple}(X) := X_0+X_1+X_2 \in \mathbb R^3$ be the sum of its columns. Let $\mathrm{cyclicCenter}$ be the triple whose $j$-th column has $-1$ in position $j$ and $1$ elsewhere, and let $\mathrm{entryBox} := \{X : |X_{j,i}-\mathrm{cyclicCenter}_{j,i}|\le 19/100 \text{ for all } j,i\}$.
--
--   For every $X\in\mathrm{entryBox}$, every triple $Z$, every weight vector $a\in\mathbb R^3$ (one weight $a_j$ per column), and every scalar $b\in\mathbb R$,
--   $$\lVert Z - b\cdot X\rVert_F^2 \;\le\; 300\left(\sum_j \lVert Z_j - a_j X_j\rVert_2^2 \;+\; \lVert \mathrm{totalTriple}(Z) - b\cdot\mathrm{totalTriple}(X)\rVert_2^2\right).$$
--
--   The left side measures how far $Z$ is from a single common rescaling $b$ of $X$. The right side allows each column its own, possibly different, rescaling $a_j$, plus one further term comparing the column sums under the shared rescaling $b$. The bound shows that controlling these per-column and total residuals separately already controls the single joint residual, which is what lets bounds proved column by column, and for the column sum, be combined into one bound for the whole triple.
--
--   **Formalization Note** The constant $300$ is a convenient, non-sharp intermediate bound: the informal write-up of this argument uses the tighter constant $110$ at the corresponding step. Using $300$ in the Lean proof simplifies the estimate and changes neither the exponent range $p\ge256$ nor the sharp constant obtained elsewhere in the construction.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/BoxGeometry.lean#L127-L166

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

theorem HlawkaSchatten.DiagonalConstruction.joint_radial_residual_bound {X : Triple} (hX : X ∈ entryBox) (Z : Triple)
    (a : Fin 3 → ℝ) (b : ℝ) :
    frobeniusSq (Z - b • X) ≤ 300 *
      (frobeniusSq (fun j ↦ Z j - a j • X j) +
        euclideanSq (totalTriple Z - b • totalTriple X)) := by sorry
