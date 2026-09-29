-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_weighted_convex_hlawka
-- name    : HlawkaSchatten.DiagonalConstruction.weighted_convex_hlawka
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T17:43:01.982703+00:00
-- url     : https://prove2.me/theorems/e14b14b4-8f5d-41e6-b1ee-0210a614aefc
-- title:
--   A weighted three-point convexity inequality, for points in any order
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{R}$ be convex on all of $\mathbb R$, and $a,b,c>0$ positive weights. For real numbers $x,y,z$, in any order, define
--   $$
--   \begin{gathered}
--   \mathrm{weightedPairs}(f,a,b,c,x,y,z) = (a+b)\,f\Big(\frac{ax+by}{a+b}\Big) \\
--   + (a+c)\,f\Big(\frac{ax+cz}{a+c}\Big) + (b+c)\,f\Big(\frac{by+cz}{b+c}\Big),
--   \end{gathered}
--   $$
--   $$
--   \mathrm{weightedTotal}(f,a,b,c,x,y,z) = a\,f(x)+b\,f(y)+c\,f(z) + (a+b+c)\,f\Big(\frac{ax+by+cz}{a+b+c}\Big).
--   $$
--
--   Then
--   $$
--   \mathrm{weightedPairs}(f,a,b,c,x,y,z) \;\le\; \mathrm{weightedTotal}(f,a,b,c,x,y,z).
--   $$
--
--   This gives the fully general, unordered form of a weighted three-point convexity inequality: for any convex real function and any positive weights, it holds for the three points however they happen to be ordered. It is the single scalar engine later applied, coordinate by coordinate, to the convex power function $t\mapsto|t|^p$, producing the dimension-independent power estimate that confines a hypothetical counterexample to the sharp Hlawka bound.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/WeightedConvex.lean#L183-L206

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_WeightedConvex
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# A weighted three-point convexity inequality

The scalar input to the sharp construction is a weighted Hlawka inequality
for any convex function on the real line. The proof uses chords and orders
the three points; it needs no integral representation of convex functions.
-/

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.weighted_convex_hlawka {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x y z : ℝ) :
    weightedPairs f a b c x y z ≤ weightedTotal f a b c x y z := by sorry
