-- Prove2me | Theorems.Thm_HlawkaSchatten_convexOn_abs_rpow
-- name    : HlawkaSchatten.convexOn_abs_rpow
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:07:10.331088+00:00
-- url     : https://prove2.me/theorems/894e53b8-e12e-4d44-8bd8-134b1a918b1d
-- title:
--   The absolute-value power $|x|^p$ is convex on $\mathbb R$ for every $p \ge 1$
-- statement:
--   Let $p \in \mathbb R$ with $p \ge 1$. Then
--
--   $$
--   x \mapsto |x|^{p} \text{ is convex on all of } \mathbb R.
--   $$
--
--   This is the elementary convexity fact underlying the scalar Bregman comparison built from the power potential $F_p(x)=|x|^p/p$ (`powerPotential`): since $p \ge 1 > 0$, dividing a convex function by $p$ preserves convexity, so this theorem also gives convexity of $F_p$, and, for $p>1$, in turn nonnegativity of its Bregman divergence $\beta_p(a,b)=F_p(a)-F_p(b)-G_p(b)(a-b)$, where $G_p(x)=|x|^{p-2}x$ (`powerGradient`) is $F_p$'s gradient.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarBregman.lean#L222-L241

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Scalar power Bregman data

These are the scalar objects used in the first layer of the audited
Bregman--Mazur proof. The normalization of `powerPotential` is important:
its derivative is the signed `(p - 1)`-power with no extra factor of `p`.
-/


open Filter
open scoped Topology

theorem HlawkaSchatten.convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by sorry
