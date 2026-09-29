-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_convex_entryBox
-- name    : HlawkaSchatten.DiagonalConstruction.convex_entryBox
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T17:18:57.955102+00:00
-- url     : https://prove2.me/theorems/27d7e20e-1133-47bf-a71c-26699834af1e
-- title:
--   Convexity of the cyclic coordinate box
-- statement:
--   Write a *triple* $X$ as three columns $X_0,X_1,X_2\in\mathbb R^3$, with $X_{j,i}$ coordinate $i$ of column $j$ (Lean: `X j i`). Let $\mathrm{cyclicCenter}$ be the triple whose $j$-th column has $-1$ in position $j$ and $1$ in the other two positions (columns $(-1,1,1)$, $(1,-1,1)$, $(1,1,-1)$), and let
--   $$\mathrm{entryBox} := \{X : |X_{j,i} - \mathrm{cyclicCenter}_{j,i}| \le 19/100 \text{ for all } j, i\}.$$
--
--   This theorem shows $\mathrm{entryBox}$ is convex as a subset of the real vector space of triples: for every $X,Y\in\mathrm{entryBox}$ and every $a,b\ge0$ with $a+b=1$, the entrywise combination $aX+bY$ again lies in $\mathrm{entryBox}$,
--   $$X,Y\in\mathrm{entryBox},\ a,b\ge0,\ a+b=1 \;\Longrightarrow\; aX+bY\in\mathrm{entryBox}.$$
--
--   $\mathrm{entryBox}$ is an axis-aligned box (a product of $9$ real intervals) centered at $\mathrm{cyclicCenter}$, so its convexity is elementary; recording it licenses averaging — any convex combination of finitely many triples already in the box again lies in the box, so a property established throughout the box applies to such an average as well. $\mathrm{entryBox}$ is also invariant under simultaneously permuting the three vector labels and the three coordinate labels by a common permutation of $\{0,1,2\}$, since $\mathrm{cyclicCenter}_{j,i}$ depends only on whether $i=j$, which such a joint relabeling preserves — though permuting one set of labels alone (the vectors, or the coordinates) need not preserve the box.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/OrbitAveraging.lean#L13-L27

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Simultaneous permutation averaging on the cyclic box -/

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.convex_entryBox : Convex ℝ entryBox := by sorry
