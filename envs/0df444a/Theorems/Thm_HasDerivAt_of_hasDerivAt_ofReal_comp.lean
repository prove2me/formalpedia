-- Prove2me | Theorems.Thm_HasDerivAt_of_hasDerivAt_ofReal_comp
-- name    : HasDerivAt.of_hasDerivAt_ofReal_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:32:17.349427+00:00
-- url     : https://prove2.me/theorems/798030a1-8598-4bb5-95ba-c7e89466b929
-- title:
--   A derivative of a complexified real function is itself real
-- statement:
--   Let $f : \mathbb{R} \to \mathbb{R}$, let $z \in \mathbb{R}$, and let $u \in \mathbb{C}$. Suppose the complexified function $y \mapsto (f(y) : \mathbb{C})$ has derivative $u$ at $z$ (in the sense of `HasDerivAt` over $\mathbb{R}$). Then $u$ is real and is a derivative of $f$: there exists $u' \in \mathbb{R}$ such that
--   $$u = u' \quad (\text{as complex numbers}) \qquad \text{and} \qquad f'(z) = u'.$$
--
--   Intuitively, a function taking values in the real axis of $\mathbb{C}$ can only have a real derivative, and that derivative is exactly the real derivative of $f$. The statement packages both the realness of $u$ and the corresponding `HasDerivAt` fact for $f$.
--
--   This descent lemma complements the complexification lemmas in the PNT+ auxiliary toolbox: after differentiating a complex-valued expression (say, inside a Mellin transform computation), one can pull the derivative back to the real-variable world with its exact value, keeping constants explicit.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Auxiliary.lean#L51-L60

/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
### Auxiliary lemmas
-/

open Complex
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

open Complex ContinuousLinearMap

theorem HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by sorry
