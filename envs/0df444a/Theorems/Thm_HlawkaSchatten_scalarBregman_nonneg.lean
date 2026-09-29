-- Prove2me | Theorems.Thm_HlawkaSchatten_scalarBregman_nonneg
-- name    : HlawkaSchatten.scalarBregman_nonneg
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:20:56.69105+00:00
-- url     : https://prove2.me/theorems/618ac5c1-5bc0-4731-b1f0-7b720b8c3816
-- title:
--   The scalar Bregman divergence of the power potential $|x|^p/p$ is nonnegative
-- statement:
--   Let $p \in \mathbb R$ with $p>1$, and let $a,b \in \mathbb R$. Write $F_p(x)=|x|^p/p$ (`powerPotential`), $G_p(x)=|x|^{p-2}x$ (`powerGradient`), and
--
--   $$
--   \beta_p(a,b) = F_p(a) - F_p(b) - G_p(b)(a-b)
--   $$
--
--   (`scalarBregman`) for the Bregman divergence of $F_p$ between $a$ and $b$. Then
--
--   $$
--   0 \le \beta_p(a,b).
--   $$
--
--   This supplies the scalar nonnegativity used in the spectral Bregman argument. There, the operator quantity is written as a sum of scalar Bregman terms with nonnegative weights, so this result gives nonnegativity of the whole sum.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarBregman.lean#L263-L287

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

theorem HlawkaSchatten.scalarBregman_nonneg {p : ℝ} (hp : 1 < p) (a b : ℝ) :
    0 ≤ scalarBregman p a b := by sorry
