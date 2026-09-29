-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_hasDerivAt_normSlope_line
-- name    : HlawkaSchatten.DiagonalConstruction.hasDerivAt_normSlope_line
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:44:40.052064+00:00
-- url     : https://prove2.me/theorems/a92a1834-ab0b-4ca9-8ffd-b08309fbfa64
-- title:
--   The norm Hessian as the second derivative of the finite coordinate norm along a line
-- statement:
--   For a finite index set $\iota$ and $p>4$, define for $v,h:\iota\to\mathbb R$
--   $$
--   \begin{gathered}
--   \mathrm{powerSum}_p(v)=\sum_i|v_i|^p,\qquad \mathrm{powerPair}_p(v,h)=\sum_i|v_i|^{p-2}v_ih_i, \\
--   \qquad \mathrm{normSlope}_p(v,h)=\mathrm{powerSum}_p(v)^{1/p-1}\,\mathrm{powerPair}_p(v,h),
--   \end{gathered}
--   $$
--   and
--   $$
--   \begin{gathered}
--   \mathrm{radialCoefficient}_p(v,h) = \frac{\mathrm{powerPair}_p(v,h)}{\mathrm{powerSum}_p(v)}, \\
--   \qquad \mathrm{normHessian}_p(v,h) = (p-1)\,\mathrm{powerSum}_p(v)^{1/p-1}\sum_i|v_i|^{p-2}\bigl(h_i-\mathrm{radialCoefficient}_p(v,h)\,v_i\bigr)^2.
--   \end{gathered}
--   $$
--
--   For $v,h:\iota\to\mathbb R$ and $t\in\mathbb R$ such that the point $v+t\cdot h$ is nonzero, this theorem shows that the real function
--   $$s \longmapsto \mathrm{normSlope}_p(v+s\,h,\,h)$$
--   has derivative $\mathrm{normHessian}_p(v+t\,h,\,h)$ at $s=t$.
--
--   The same expression $\mathrm{normSlope}_p(v,h)$ is, for $v\ne0$, the ordinary first derivative at $s=0$ of $s\mapsto\bigl(\sum_i|v_i+sh_i|^p\bigr)^{1/p}$, the finite coordinate $p$-norm of $v+sh$ (differentiating $|v_i+sh_i|^p$ termwise and applying the chain rule for the outer power $1/p$, valid once $v\ne0$ makes the sum inside positive). This theorem supplies the corresponding fact one derivative further, so $\mathrm{normHessian}_p$ is exactly the second derivative — the curvature — of the finite coordinate $p$-norm along a line, at any point away from the origin.
--
--   **Formalization Note** The hypothesis $v+t\cdot h\ne0$ is used only to keep $\mathrm{powerSum}_p(v+th)=\sum_i|v_i+th_i|^p$ positive, so that raising it to the exponent $1/p-1$ behaves as the ordinary reciprocal power. The coordinatewise term $|x|^{p-2}x$ occurring inside $\mathrm{powerPair}$, and inside $\mathrm{normHessian}$'s own residual, is differentiable — with derivative $(p-1)|x|^{p-2}$ — at every real $x$ including $x=0$ (given $p>4$, as assumed here), so no individual coordinate of $v+th$ needs to avoid zero.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/NormHessian.lean#L148-L165

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Directional second derivatives of the finite real coordinate norm -/


variable {ι : Type*} [Fintype ι]

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.hasDerivAt_normSlope_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ normSlope p (v + s • h) h) (normHessian p (v + t • h) h) t := by sorry
