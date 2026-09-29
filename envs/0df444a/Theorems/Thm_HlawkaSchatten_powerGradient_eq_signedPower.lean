-- Prove2me | Theorems.Thm_HlawkaSchatten_powerGradient_eq_signedPower
-- name    : HlawkaSchatten.powerGradient_eq_signedPower
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:18:38.961967+00:00
-- url     : https://prove2.me/theorems/92ffa00a-ab31-45a7-a088-554052c55885
-- title:
--   The power gradient $|x|^{p-2}x$ equals the signed $(p-1)$-power of $x$
-- statement:
--   Let $p,x \in \mathbb R$. Write $G_p(x) = |x|^{p-2}x$ (`powerGradient`), and write $\mathrm{signedPower}(q,x)=\operatorname{sgn}(x)\,|x|^{q}$ for the signed $q$-th power of $x$ (with $\operatorname{sgn}(0)=0$). Then
--
--   $$
--   G_p(x) = \mathrm{signedPower}(p-1,\,x).
--   $$
--
--   For $p>1$, $G_p(\cdot)$ is the derivative of the power potential $F_p(t)=|t|^p/p$ (`powerPotential`); this identity rewrites that derivative as the signed $(p-1)$-power $\operatorname{sgn}(x)|x|^{p-1}$, with no extra factor of $p$. It is the starting point for the scalar Bregman divergence $\beta_p(a,b)=F_p(a)-F_p(b)-G_p(b)(a-b) = |a|^p/p - |b|^p/p - G_p(b)(a-b)$ built from the power potential, and it sits alongside the Euler-type identity $x\,G_p(x) = |x|^p = p\,F_p(x)$, valid for $p>0$; facts about $G_p$ such as its strict monotonicity for $p>1$ and its oddness ($G_p(-x)=-G_p(x)$) are derived by rewriting through this equation to the better-understood signed power function.
--
--   **Formalization Note.** The identity holds for every real $p$ and $x$: the real power is a total function (with $0^r = 0$ for $r \neq 0$ and $0^0 = 1$), and at $x=0$ both sides vanish because of the factor $x$ on the left and $\operatorname{sgn}(0)=0$ on the right. It is $G_p$'s role as the derivative of $F_p$ -- not this algebraic identity -- that needs $p>1$: for $p \le 1$ the two sides remain equal, but $G_p$ is then no longer the derivative of $F_p$ on all of $\mathbb R$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarBregman.lean#L58-L75

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

theorem HlawkaSchatten.powerGradient_eq_signedPower (p x : ℝ) :
    powerGradient p x = signedPower (p - 1) x := by sorry
