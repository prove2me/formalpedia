-- Prove2me | Theorems.Thm_HlawkaSchatten_scalarBregman_pos
-- name    : HlawkaSchatten.scalarBregman_pos
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:24:53.609343+00:00
-- url     : https://prove2.me/theorems/0ebbaf08-011b-413f-9247-81063d39b309
-- title:
--   The scalar Bregman divergence of the power potential $|x|^p/p$ is strictly positive off the diagonal
-- statement:
--   Let $p \in \mathbb R$ with $p>1$, and let $a,b \in \mathbb R$ with $a \neq b$. Write $F_p(x)=|x|^p/p$ (`powerPotential`), $G_p(x)=|x|^{p-2}x$ (`powerGradient`), and
--
--   $$
--   \beta_p(a,b) = F_p(a) - F_p(b) - G_p(b)(a-b)
--   $$
--
--   (`scalarBregman`) for the Bregman divergence of $F_p$ between $a$ and $b$. Then
--
--   $$
--   0 < \beta_p(a,b).
--   $$
--
--   This sharpens nonnegativity to strict positivity at every pair of distinct scalar arguments. It does not supply a uniform positive lower bound over all such pairs. Uniform comparison constants relating this divergence to the squared scalar Mazur distance require separate estimates for their ratio, including its limiting regimes.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarBregman.lean#L289-L312

import Definitions.Def_HlawkaSchatten_ScalarBregman
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

open HlawkaSchatten

theorem HlawkaSchatten.scalarBregman_pos {p : ℝ} (hp : 1 < p) {a b : ℝ} (hab : a ≠ b) :
    0 < scalarBregman p a b := by sorry
