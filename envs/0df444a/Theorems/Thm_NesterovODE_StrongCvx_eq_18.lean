-- Prove2me | Theorems.Thm_NesterovODE_StrongCvx_eq_18
-- name    : NesterovODE.StrongCvx.eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:12.628732+00:00
-- url     : https://prove2.me/theorems/378080b9-0c5d-451a-bdca-ed2321fe12f0
-- title:
--   (18), p. 13 — derivative of the high-friction energy
-- statement:
--   Let $f\in\mathcal F_L$, let $r>1$, and let $x^\star$ minimize $f$. For a solution $(X,V)$ of (17), the high-friction energy $E_5$ has, at every $t>0$, derivative
--
--   $$\dot E_5(t)=\frac{4t}{r-1}(f(X(t))-f^\star)-2t\langle X(t)-x^\star,\nabla f(X(t))\rangle\leq-\frac{2(r-3)t}{r-1}(f(X(t))-f^\star).$$
--
--   This is the differential estimate used to obtain Theorem 5. The inequality follows from the stated convexity class.
--
--   **Formalization Note** The paper works in $\mathcal F_\infty$ here. An explicit positive Lipschitz constant $L$ witnesses that membership. Solutions are quantified rather than selected by uniqueness.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 13, (18)

import Mathlib
import Definitions.Def_NesterovODE_StrongCvx_Setting

namespace NesterovODE.StrongCvx

/-- Equation (18), including the exact energy derivative and its convexity bound. -/
theorem eq_18 (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (L : NNReal) (r : ℝ)
    (x₀ xstar : NesterovODE.WellPosed.E n) (X V : ℝ → NesterovODE.WellPosed.E n)
    (hL : 0 < L) (hf : InFL L f) (hr : 1 < r)
    (hmin : ∀ y, f xstar ≤ f y)
    (hX : IsSolution f r x₀ X V)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => energy5 f r xstar X V u)
      (4 * t / (r - 1) * (f (X t) - f xstar) -
        2 * t * inner ℝ (X t - xstar) (gradient f (X t))) t ∧
      4 * t / (r - 1) * (f (X t) - f xstar) -
        2 * t * inner ℝ (X t - xstar) (gradient f (X t)) ≤
        -(2 * (r - 3) * t / (r - 1)) * (f (X t) - f xstar) := by sorry

end NesterovODE.StrongCvx
