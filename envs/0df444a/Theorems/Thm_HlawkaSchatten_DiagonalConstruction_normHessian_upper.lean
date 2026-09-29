-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normHessian_upper
-- name    : HlawkaSchatten.DiagonalConstruction.normHessian_upper
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:18:12.319689+00:00
-- url     : https://prove2.me/theorems/b0ffa235-f62d-4c03-8bf4-cf1d50658740
-- title:
--   A uniform upper bound $d_p$ for the norm Hessian at a near-coordinate vector
-- statement:
--   For $v,h\in\mathbb R^3$, define
--   $$\mathrm{powerSum}_p(v):=\sum_i|v_i|^p,\qquad \mathrm{radialCoefficient}_p(v,h):=\frac{\sum_i|v_i|^{p-2}v_ih_i}{\mathrm{powerSum}_p(v)},$$
--   $$\mathrm{normHessian}_p(v,h):=(p-1)\,\mathrm{powerSum}_p(v)^{1/p-1}\sum_i|v_i|^{p-2}\bigl(h_i-\mathrm{radialCoefficient}_p(v,h)\,v_i\bigr)^2,$$
--   and for $p>2$ define
--   $$d_p := \frac{2(p-1)(19/50)^{p-2}}{(81/50)^{p-1}}.$$
--
--   For every $p>2$, every $v,h\in\mathbb R^3$, and every coordinate $k\in\{0,1,2\}$ such that $v_k$ is large, $81/50\le|v_k|$, while every other coordinate is small, $|v_i|\le19/50$ for $i\ne k$,
--   $$\mathrm{normHessian}_p(v,h) \;\le\; d_p\,\lVert h\rVert_2^2,\qquad \lVert h\rVert_2^2=\textstyle\sum_ih_i^2.$$
--
--   This is a uniform upper curvature bound for the finite coordinate $p$-norm's Hessian, at a vector with one dominant, nearly saturated coordinate and two small ones — the shape taken, for instance, by a pairwise column sum such as $X_0+X_1$ of a triple confined to a box around the cyclic sign pattern.
--
--   **Formalization Note** No hypothesis that $v\ne0$ is needed: $81/50\le|v_k|$ already forces $v_k\ne0$, hence $\mathrm{powerSum}_p(v)>0$, so $\mathrm{normHessian}_p(v,h)$ is well-defined without a division-by-zero or zero-to-a-negative-power issue, even though the other two coordinates of $v$ may vanish.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/HessianBounds.lean#L102-L145

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_HessianBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
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

/-! # Uniform lower and upper bounds for the norm Hessian -/

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.normHessian_upper {p : ℝ} (hp : 2 < p) (v h : Fin 3 → ℝ) (k : Fin 3)
    (hk : 81 / 50 ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ 19 / 50) :
    normHessian p v h ≤ upperHessianCoefficient p * euclideanSq h := by sorry
