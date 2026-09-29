-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three
-- name    : HlawkaSchatten.DiagonalConstruction.real_bound_of_fin_three
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:52:24.275981+00:00
-- url     : https://prove2.me/theorems/9face38e-b769-47bf-99b7-b0ab3a1f86bc
-- title:
--   Lifting a three-coordinate Hlawka bound to every finite real dimension
-- statement:
--   For a finite index set $\iota$ and a real vector $v:\iota\to\mathbb R$, write $\|v\|_p:=\big(\sum_{i\in\iota}|v_i|^p\big)^{1/p}$ (`lpNorm`) for the coordinate $p$-norm. For real vectors $u,v,w$ on a common index set, write the triple deficit
--   $$
--   \mathrm{tripleGap}(u,v,w) = \|u\|_p+\|v\|_p+\|w\|_p-\|u+v+w\|_p,
--   $$
--   and the pair-deficit sum $\mathrm{pairGapSum}(u,v,w)$ for the sum of the three pair deficits $\|a\|_p+\|b\|_p-\|a+b\|_p$ over $\{u,v\},\{u,w\},\{v,w\}$. Say $\|\cdot\|_p$ *has Hlawka constant* $C$ (`HasHlawkaConstant`) when
--   $$
--   \mathrm{tripleGap}(u,v,w) \le C\cdot\mathrm{pairGapSum}(u,v,w) \qquad\text{for all }u,v,w.
--   $$
--
--   Let $\iota$ be any finite index set, $p>1$, and $K\ge\tfrac12$. Suppose $\|\cdot\|_p$ has Hlawka constant $K$ on three real coordinates:
--   $$
--   \mathrm{tripleGap}(u,v,w) \le K\cdot\mathrm{pairGapSum}(u,v,w) \qquad\text{for all }u,v,w:\mathrm{Fin}\,3\to\mathbb R.
--   $$
--
--   Then $\|\cdot\|_p$ has Hlawka constant $K$ on $\iota\to\mathbb R$ too:
--   $$
--   \mathrm{tripleGap}(x,y,z) \le K\cdot\mathrm{pairGapSum}(x,y,z) \qquad\text{for all }x,y,z:\iota\to\mathbb R.
--   $$
--
--   This is the dimension-independence half of the sharp diagonal construction on the real side: an admissible Hlawka constant for three real coordinates is automatically admissible in every finite real dimension, with no dependence on the size of $\iota$. Combined with the fact that the explicit cyclic constant $K_p=\sup_{1/2\le t\le2}R_p(t)$ (`cyclicConstant`; $R_p(t)$ is the ratio of triple deficit to pair-deficit sum for the triple $(-t,1,1),(1,-t,1),(1,1,-t)$) is such a three-coordinate constant for every real $p\ge256$ (established elsewhere) and the later complex transfer step, this is what allows the Hlawka bound with constant $K_p$ for diagonal Schatten $p$-norms to hold in every finite dimension, including dimension zero.
--
--   **Formalization Note** $\iota$ ranges over an arbitrary finite type (via a `Fintype` instance), not just `Fin n`, and may be empty.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/DimensionReduction.lean#L100-L126

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
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
# Reduction of a failed bound to three real coordinates

Common coordinate weights preserve the three pair power sums. The positive
part of the target inequality is concave in these weights, so the sparse
minimizer lemma reduces the question to at most three nonzero coordinates.
-/


variable {ι : Type*} [Fintype ι]

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.real_bound_of_fin_three {p K : ℝ} (hp : 1 < p) (hK : 1 / 2 ≤ K)
    (h3 : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) K) :
    HasHlawkaConstant (lpNorm p : (ι → ℝ) → ℝ) K := by sorry
