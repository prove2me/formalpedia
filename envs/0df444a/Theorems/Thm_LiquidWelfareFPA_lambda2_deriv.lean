-- Prove2me | Theorems.Thm_LiquidWelfareFPA_lambda2_deriv
-- name    : LiquidWelfareFPA.lambda2_deriv
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:42.696388+00:00
-- url     : https://prove2.me/theorems/9875ad5f-df77-418b-996e-ddce98dad8a1
-- title:
--   Appendix A, p.22 — $d\lambda_2/d\gamma<0$
-- statement:
--   For every $\gamma\ge1$, write $w=W(-e^{-2/\gamma}/\gamma)$. Then $\lambda_2$ is differentiable at $\gamma$ with
--
--   $$\frac{d\lambda_2}{d\gamma}\ =\ \frac{w}{\gamma}\cdot\frac{2+\gamma w}{1+w}\ <\ 0,$$
--
--   and $\lambda_2$ is strictly decreasing on $[1,\infty)$. This is the monotonicity used to prove (12).
--
--   Differences from the source: none.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, Appendix A, p.22

import Mathlib
import Definitions.Def_LiquidWelfareFPA_lam2

namespace LiquidWelfareFPA

/-- **The derivative of `λ₂` is negative.**
Fikioris & Tardos, arXiv:2210.07502v4, Appendix A, p.22: "The derivative of λ2 (calculated in
Mathematica) is dλ2/dγ = (W(−e^{−2/γ}/γ)/γ) · (2 + γW(−e^{−2/γ}/γ))/(1 + W(−e^{−2/γ}/γ)). The above
quantity is strictly negative", and "We do both of these by proving that λ2 is decreasing in γ."

For every `γ ≥ 1`, with `w = W(−e^{−2/γ}/γ)`: `λ₂` has derivative `(w/γ)·(2 + γw)/(1 + w)` at
`γ`, this number is `< 0`, and `λ₂` is strictly decreasing on `[1, ∞)`. -/
theorem lambda2_deriv :
    (∀ γ : ℝ, 1 ≤ γ →
      HasDerivAt lam2
        (lambertW (-Real.exp (-2 / γ) / γ) / γ *
          ((2 + γ * lambertW (-Real.exp (-2 / γ) / γ)) / (1 + lambertW (-Real.exp (-2 / γ) / γ))))
        γ ∧
      lambertW (-Real.exp (-2 / γ) / γ) / γ *
          ((2 + γ * lambertW (-Real.exp (-2 / γ) / γ)) / (1 + lambertW (-Real.exp (-2 / γ) / γ)))
        < 0) ∧
    StrictAntiOn lam2 (Set.Ici 1) := by sorry

end LiquidWelfareFPA
