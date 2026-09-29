-- Prove2me | Theorems.Thm_HlawkaSchatten_continuous_signedPower
-- name    : HlawkaSchatten.continuous_signedPower
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:17:43.154236+00:00
-- url     : https://prove2.me/theorems/91a7d2a5-56d4-498d-87f6-277f97526b63
-- title:
--   The signed power $x \mapsto \operatorname{sgn}(x)\,|x|^{q}$ is continuous for every exponent $q>0$
-- statement:
--   Let $q \in \mathbb R$ with $q > 0$. For $x \in \mathbb R$ write
--
--   $$
--   \mathrm{signedPower}(q,x) = \operatorname{sgn}(x)\,|x|^{q},
--   $$
--
--   using the convention $\operatorname{sgn}(0) = 0$ and the real power $|x|^q$ (with $0^q = 0$ since $q \neq 0$). Then
--
--   $$
--   x \mapsto \mathrm{signedPower}(q,x) \text{ is continuous on } \mathbb R.
--   $$
--
--   The sign function alone is discontinuous at $0$, jumping between $-1$ and $1$; multiplying it by $|x|^q$ removes the jump once $q>0$. This makes $\mathrm{signedPower}(q,\cdot)$ a continuous odd extension of $x \mapsto x^q$ to negative $x$; together with its strict monotonicity (`strictMono_signedPower`) and unboundedness, continuity is what lets it serve as a global change of variables -- for instance the scalar Mazur map $\psi_p(x) = \mathrm{signedPower}(p/2,x)$ for $p>0$, used to compare a power geometry with a Hilbert (squared-distance) geometry.
--
--   **Formalization Note.** Both $\operatorname{sgn}$ and the real power $|x|^q$ are totalized on all of $\mathbb R$: $\operatorname{sgn}(0)=0$, and $0^q=0$ for $q\neq0$. These conventions make the continuity claim well-defined at $x=0$ without any case split on the definition itself.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarBregman.lean#L165-L192

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

theorem HlawkaSchatten.continuous_signedPower {q : ℝ} (hq : 0 < q) : Continuous (signedPower q) := by sorry
