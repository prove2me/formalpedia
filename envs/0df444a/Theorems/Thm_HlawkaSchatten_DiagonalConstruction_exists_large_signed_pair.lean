-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_large_signed_pair
-- name    : HlawkaSchatten.DiagonalConstruction.exists_large_signed_pair
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:23:32.033028+00:00
-- url     : https://prove2.me/theorems/f4967831-6999-46c6-8a42-9d1567145ce9
-- title:
--   A common near-saturating coordinate for a close pair, in three real dimensions
-- statement:
--   For a real exponent $p\ge256$ and two vectors $x,y:\mathrm{Fin}\,3\to\mathbb R$ (three real coordinates), write
--   $$
--   \|v\|_p=\Big(\sum_i|v_i|^p\Big)^{1/p}
--   $$
--   for the coordinate $p$-norm, and $\mathrm{pairGap}(x,y)=\|x\|_p+\|y\|_p-\|x+y\|_p$ for the pair deficit.
--
--   Suppose
--   $$
--   \|x\|_p<\tfrac{53}{150},\qquad \|y\|_p<\tfrac{53}{150},\qquad \mathrm{pairGap}(x,y)<\tfrac2p.
--   $$
--
--   Then there is a coordinate $i\in\mathrm{Fin}\,3$ and a common sign $s\in\{1,-1\}$ such that both entries $x_i$ and $y_i$, after multiplication by $s$, nearly saturate their respective norms:
--   $$
--   \|x\|_p - \frac{14}{5p} < s\,x_i, \qquad \|y\|_p - \frac{14}{5p} < s\,y_i.
--   $$
--
--   A small pair deficit gives one common coordinate and one choice of sign for which each signed entry is within $14/(5p)$ below its vector's norm. This alone need not make both signed entries positive when a vector is very small. In the later confined-counterexample setting, the additional lower bounds on the norms do make them positive. Applied to each of the three pairs $(x,y),(x,z),(y,z)$ arising from a confined strict counterexample, it is the mechanism that pins down a shared coordinate pattern for the whole triple, which is then reorganized into a fixed cyclic coordinate box.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Coordinates.lean#L44-L96

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
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

/-! # Large pair coordinates and signed coordinate permutations -/

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.exists_large_signed_pair {p : ℝ} (hp : 256 ≤ p) (x y : Fin 3 → ℝ)
    (hx : lpNorm p x < 53 / 150) (hy : lpNorm p y < 53 / 150)
    (hgap : pairGap (lpNorm p) x y < 2 / p) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      lpNorm p x - 14 / (5 * p) < s * x i ∧
      lpNorm p y - 14 / (5 * p) < s * y i := by sorry
