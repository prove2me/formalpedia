-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normHessian_lower
-- name    : HlawkaSchatten.DiagonalConstruction.normHessian_lower
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:14:23.383735+00:00
-- url     : https://prove2.me/theorems/75e8f201-2385-4197-bcf3-8557d15913a9
-- title:
--   A uniform lower bound $b_p$ for the finite coordinate norm's Hessian
-- statement:
--   For $v,h\in\mathbb R^3$, define
--   $$
--   \begin{gathered}
--   \mathrm{powerSum}_p(v):=\sum_i|v_i|^p,\qquad \mathrm{powerPair}_p(v,h):=\sum_i|v_i|^{p-2}v_ih_i, \\
--   \qquad \mathrm{radialCoefficient}_p(v,h):=\frac{\mathrm{powerPair}_p(v,h)}{\mathrm{powerSum}_p(v)},
--   \end{gathered}
--   $$
--   $$\mathrm{normHessian}_p(v,h):=(p-1)\,\mathrm{powerSum}_p(v)^{1/p-1}\sum_i|v_i|^{p-2}\bigl(h_i-\mathrm{radialCoefficient}_p(v,h)\,v_i\bigr)^2,$$
--   and for $p>2$ define
--   $$b_p := \frac{(p-1)(43/100)^{p-2}}{3\,(157/100)^{p-1}}.$$
--
--   For every $p>2$ and every $v,h\in\mathbb R^3$ whose entries satisfy $43/100\le|v_i|\le157/100$ for every coordinate $i$,
--   $$
--   \begin{gathered}
--   b_p\, \lVert h - \mathrm{radialCoefficient}_p(v,h)\cdot v\rVert_2^2 \;\le\; \mathrm{normHessian}_p(v,h), \\
--   \qquad \lVert w\rVert_2^2:=\textstyle\sum_iw_i^2.
--   \end{gathered}
--   $$
--
--   This is a uniform lower curvature bound for the finite coordinate $p$-norm's Hessian, valid at any vector $v$ whose entries all stay within a fixed range around $\pm1$. The bound is nonnegative but not everywhere positive: $h-\mathrm{radialCoefficient}_p(v,h)v$, the part of $h$ transverse to $v$ in this weighted sense, vanishes exactly when $h$ is itself a scalar multiple of $v$, so the curvature genuinely degenerates in that radial direction even though $\mathrm{normHessian}_p(v,h)$ itself stays $\ge b_p\cdot 0=0$.
--
--   **Formalization Note** No hypothesis that $v\ne0$ is needed: $43/100\le|v_i|$ for every $i$ already forces every $v_i\ne0$, hence $\mathrm{powerSum}_p(v)>0$, so the exponent $1/p-1$ causes no division-by-zero or zero-to-a-negative-power issue.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/HessianBounds.lean#L43-L75

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

theorem HlawkaSchatten.DiagonalConstruction.normHessian_lower {p : ℝ} (hp : 2 < p) (v h : Fin 3 → ℝ)
    (hlo : ∀ i, 43 / 100 ≤ |v i|) (hhi : ∀ i, |v i| ≤ 157 / 100) :
    lowerHessianCoefficient p * euclideanSq (h - radialCoefficient p v h • v) ≤
      normHessian p v h := by sorry
