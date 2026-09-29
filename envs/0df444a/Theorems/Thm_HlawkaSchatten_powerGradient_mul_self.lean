-- Prove2me | Theorems.Thm_HlawkaSchatten_powerGradient_mul_self
-- name    : HlawkaSchatten.powerGradient_mul_self
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:20:41.967567+00:00
-- url     : https://prove2.me/theorems/a826af4b-c400-4188-8284-9dbc70a281cc
-- title:
--   Euler's identity for the power potential $F_p$ and its gradient $G_p$
-- statement:
--   Let $p \in \mathbb R$ with $p>0$, and let $x \in \mathbb R$. Write $F_p(x) = |x|^p/p$ (`powerPotential`) and $G_p(x) = |x|^{p-2}x$ (`powerGradient`). Then
--
--   $$
--   G_p(x)\cdot x = p \cdot F_p(x).
--   $$
--
--   Equivalently, since $p\cdot F_p(x) = |x|^p$, the gradient times $x$ recovers $|x|^p$ exactly. This is the Euler identity for the potential $F_p$, which is positively homogeneous of degree $p$: multiplying its gradient by $x$ recovers $p$ times the potential itself. It is an algebraic bookkeeping fact used to simplify expressions that mix the power gradient and the power potential at the same point, arising when the Bregman divergence's defining formula is expanded and rearranged.
--
--   **Formalization Note.** The identity holds for every $p>0$ and every real $x$, including $x=0$ (both sides vanish) and the range $0<p\le1$, where $G_p(\cdot)$ is a totalized algebraic convention rather than an actual derivative of $F_p$ at the origin: $F_p$ itself is not differentiable at $0$ when $p\le1$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarBregman.lean#L354-L368

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

theorem HlawkaSchatten.powerGradient_mul_self {p : ℝ} (hp : 0 < p) (x : ℝ) :
    powerGradient p x * x = p * powerPotential p x := by sorry
