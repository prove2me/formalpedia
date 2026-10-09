-- Prove2me | Theorems.Thm_NesterovODE_StrongCvx_eq_24
-- name    : NesterovODE.StrongCvx.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:57.878977+00:00
-- url     : https://prove2.me/theorems/5979dc6f-1325-42db-8f4a-18b99af27056
-- title:
--   (24), p. 18 — integrated strongly convex energy bound
-- statement:
--   Let $f\in\mathcal S_{\mu,L}$ with $\mu>0$, let $\alpha>2$ and $\alpha\leq2r/3$, and let $(X,V)$ solve (17) with minimizer $x^\star$. Write $t_\alpha=\sqrt{(\alpha-2)(2r-\alpha)/(2\mu)}$. For every $t\geq t_\alpha$, equation (24) gives an integrated bound on $E_8(t;\alpha)$ and the two ensuing estimates:
--
--   $$E_8(t;\alpha)\leq E_8(t_\alpha;\alpha)+\frac{(\alpha-2)(2r-\alpha)t^{\alpha-2}}8\|X(t)-x^\star\|^2\leq E_8(t_\alpha;\alpha)+\frac{(\alpha-2)(2r-\alpha)t^{\alpha-2}}{4\mu}(f(X(t))-f^\star).$$
--
--   The integrated inequality retains its endpoint and nonnegative integral terms in the formal statement. This result connects the stronger energy to the objective error at later times.
--
--   **Formalization Note** Positive $\mu$ and $\alpha>2$ make $t_\alpha$ positive. The integral on $[t_\alpha,t]$ is explicitly required to be integrable. The ODE is quantified over all its solutions.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, pp. 17–18, (24)

import Mathlib
import Definitions.Def_NesterovODE_StrongCvx_Setting

namespace NesterovODE.StrongCvx

/-- Equation (24), including the integrated estimate and both simplifications. -/
theorem eq_24 (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (L : NNReal) (r α mu : ℝ)
    (x₀ xstar : NesterovODE.WellPosed.E n) (X V : ℝ → NesterovODE.WellPosed.E n)
    (hL : 0 < L) (hmu : 0 < mu) (hf : InSMuL mu L f)
    (ha : 2 < α) (hr : α ≤ 2 * r / 3)
    (hmin : ∀ y, f xstar ≤ f y)
    (hX : IsSolution f r x₀ X V)
    (t : ℝ) (ht : tAlpha r α mu ≤ t) :
    IntervalIntegrable
      (fun u : ℝ => (α - 2) ^ 2 * (2 * r - α) * u ^ (α - 3) *
        ‖X u - xstar‖ ^ 2) MeasureTheory.volume (tAlpha r α mu) t ∧
    energy8 f r α xstar X V t ≤
      energy8 f r α xstar X V (tAlpha r α mu) +
        (α - 2) * (2 * r - α) * t ^ (α - 2) / 8 * ‖X t - xstar‖ ^ 2 -
        (α - 2) * (2 * r - α) * (tAlpha r α mu) ^ (α - 2) / 8 *
          ‖X (tAlpha r α mu) - xstar‖ ^ 2 -
        (1 / 8 : ℝ) * (∫ u in (tAlpha r α mu)..t,
          (α - 2) ^ 2 * (2 * r - α) * u ^ (α - 3) * ‖X u - xstar‖ ^ 2) ∧
    energy8 f r α xstar X V t ≤
      energy8 f r α xstar X V (tAlpha r α mu) +
        (α - 2) * (2 * r - α) * t ^ (α - 2) / 8 * ‖X t - xstar‖ ^ 2 ∧
    energy8 f r α xstar X V t ≤
      energy8 f r α xstar X V (tAlpha r α mu) +
        (α - 2) * (2 * r - α) * t ^ (α - 2) / (4 * mu) *
          (f (X t) - f xstar) := by sorry

end NesterovODE.StrongCvx
