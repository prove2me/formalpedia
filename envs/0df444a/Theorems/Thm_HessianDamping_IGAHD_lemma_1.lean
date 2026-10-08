-- Prove2me | Theorems.Thm_HessianDamping_IGAHD_lemma_1
-- name    : HessianDamping.IGAHD.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:50.705726+00:00
-- url     : https://prove2.me/theorems/edaa8928-4b83-4489-80b0-b18cc919aea0
-- title:
--   Lemma 1 (28) — extended descent inequality
-- statement:
--   Let $f:H\to\mathbb R$ be convex and differentiable on a real Hilbert space, with an $L$-Lipschitz gradient, where $L>0$. For $0<s\le1/L$ and any $u,v\in H$,
--
--   $$f(v-s\nabla f(v))\le f(u)+\langle\nabla f(v),v-u\rangle-\frac{s}{2}\|\nabla f(v)\|^2-\frac{s}{2}\|\nabla f(u)-\nabla f(v)\|^2.$$
--
--   This strengthens the usual gradient descent bound by retaining a squared gradient-difference term. It is the input to the energy estimates for IGAHD.
--
--   **Formalization Note** Differentiability and $L>0$ are explicit so the gradient and the upper bound $1/L$ have their intended meanings.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 34, Lemma 1, (28)

import Mathlib
import Definitions.Def_HessianDamping_IGAHD_Setting

namespace HessianDamping.IGAHD

/-- Lemma 1, (28), p. 34. -/
theorem lemma_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (s : ℝ) (hs : 0 < s) (hsL : s ≤ 1 / L) :
    ∀ u v : H, f (v - s • gradient f v) ≤
      f u + inner ℝ (gradient f v) (v - u)
        - s / 2 * ‖gradient f v‖ ^ 2
        - s / 2 * ‖gradient f u - gradient f v‖ ^ 2 := by sorry
end HessianDamping.IGAHD
