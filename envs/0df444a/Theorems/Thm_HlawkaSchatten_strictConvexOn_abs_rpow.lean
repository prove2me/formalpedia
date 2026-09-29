-- Prove2me | Theorems.Thm_HlawkaSchatten_strictConvexOn_abs_rpow
-- name    : HlawkaSchatten.strictConvexOn_abs_rpow
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:24:37.941289+00:00
-- url     : https://prove2.me/theorems/58584365-99a8-48d1-b339-ae4579f08919
-- title:
--   The absolute-value power $|x|^p$ is strictly convex on $\mathbb R$ for $p>1$
-- statement:
--   Let $p \in \mathbb R$ with $p>1$. Then
--
--   $$
--   x \mapsto |x|^{p} \text{ is strictly convex on } \mathbb R.
--   $$
--
--   Strict convexity, as opposed to the plain convexity that already holds at $p=1$, is exactly what upgrades the Bregman divergence $\beta_p(a,b) = F_p(a) - F_p(b) - G_p(b)(a-b)$ of the power potential $F_p(x)=|x|^p/p$ (`powerPotential`), where $G_p(x)=|x|^{p-2}x$ (`powerGradient`), from merely nonnegative to strictly positive whenever its two arguments differ: it is the hypothesis used to show $\beta_p(a,b)>0$ for $a\neq b$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarBregman.lean#L243-L261

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

theorem HlawkaSchatten.strictConvexOn_abs_rpow {p : ℝ} (hp : 1 < p) :
    StrictConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by sorry
