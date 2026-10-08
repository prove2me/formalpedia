-- Prove2me | Theorems.Thm_HessianDamping_IGAHD_eq_18
-- name    : HessianDamping.IGAHD.eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:54.50316+00:00
-- url     : https://prove2.me/theorems/ced8d1f3-245b-4f2d-891e-9b94a2947c03
-- title:
--   Equation (18) — weighted descent inequality
-- statement:
--   Under the smooth convex assumptions of Theorem 6, let $(x_k,y_k)$ be an IGAHD run and let $x^*$ minimize $f$. At an index $k\ge1$ for which $t_{k+1}\ge1$, the paper's weighted descent estimate is
--
--   $$\begin{aligned}t_{k+1}(f(x_{k+1})-f(x^*))\le{}&(t_{k+1}-1)(f(x_k)-f(x^*))\\&+\langle\nabla f(y_k),(t_{k+1}-1)(y_k-x_k)+y_k-x^*\rangle\\&-\tfrac{s}{2}t_{k+1}\|\nabla f(y_k)\|^2-\tfrac{s}{2}(t_{k+1}-1)\|\nabla f(x_k)-\nabla f(y_k)\|^2-\tfrac{s}{2}\|\nabla f(y_k)\|^2.\end{aligned}$$
--
--   This is the displayed bridge from Lemma 1 to the Lyapunov estimate.
--
--   **Formalization Note** The condition $t_{k+1}\ge1$ is written as $k\ge\alpha-1$; the source explicitly requires $t_{k+1}-1\ge0$ when multiplying (16).
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 16, (18)

import Mathlib
import Definitions.Def_HessianDamping_IGAHD_Setting

namespace HessianDamping.IGAHD

/-- Inequality (18), p. 16, at the indices where t_{k+1} − 1 ≥ 0. -/
theorem eq_18 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : H) (hxstar : ∀ z : H, f xstar ≤ f z)
    (α β s : ℝ) (hα : 3 ≤ α) (hs : 0 < s) (hsL : s ≤ 1 / L)
    (hβ0 : 0 ≤ β) (hβs : β < 2 * Real.sqrt s)
    (x y : ℕ → H) (hrun : IsIGAHDRun f α β s x y)
    (k : ℕ) (hk : 1 ≤ k) (hkt : α - 1 ≤ (k : ℝ)) :
    tK α (k + 1) * (f (x (k + 1)) - f xstar) ≤
      (tK α (k + 1) - 1) * (f (x k) - f xstar)
      + inner ℝ (gradient f (y k)) ((tK α (k + 1) - 1) • (y k - x k) + y k - xstar)
      - s / 2 * tK α (k + 1) * ‖gradient f (y k)‖ ^ 2
      - s / 2 * (tK α (k + 1) - 1) * ‖gradient f (x k) - gradient f (y k)‖ ^ 2
      - s / 2 * ‖gradient f (y k)‖ ^ 2 := by sorry
end HessianDamping.IGAHD
