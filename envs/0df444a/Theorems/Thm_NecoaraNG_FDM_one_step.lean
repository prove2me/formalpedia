-- Prove2me | Theorems.Thm_NecoaraNG_FDM_one_step
-- name    : NecoaraNG.FDM.one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:15.70073+00:00
-- url     : https://prove2.me/theorems/f699ade4-5b44-4585-a61b-ed7a2a0be1ce
-- title:
--   Proof of Theorem 15, p. 30 — one step of (FDM) contracts f − f* by 1/(1 + Lκ_f/(4(L_f + L̄_f + βL̄_f)²))
-- statement:
--   Under the hypotheses of Theorem 15 (problem (P) with $X$ closed convex, $f$ convex on $X$ and differentiable on $X$ with $L_f$-Lipschitz gradient, a minimizer $x^*\in X^*$, quadratic functional growth (22) with constant $\kappa_f>0$, constants $\beta,L,\bar L_f>0$, and a run $(x^k),(e^k),(\alpha_k)$ of (FDM)), writing $f^*=f(x^*)$, for every $k\ge0$
--   $$
--   f(x^{k+1})-f^*\ \le\ \frac{1}{1+\dfrac{L\kappa_f}{4(L_f+\bar L_f+\beta\bar L_f)^2}}\,\big(f(x^k)-f^*\big).
--   $$
--
--   Iterating this contraction gives the linear rate (64) of Theorem 15.
--
--   **Formalization Note** The page writes the gaps as $f(x^{k+1})-f(\bar x^{k+1})$ and $f(x^k)-f(\bar x^k)$; both $f(\bar x^{k+1})$ and $f(\bar x^k)$ equal $f^*$ because $\bar x^{k+1},\bar x^k\in X^*$, so the statement uses $f^*=f(x^*)$ for a fixed minimizer $x^*$. The page's last display prints $L_f+L_f+\beta L_f$ in the denominator; the constant here is $L_f+\bar L_f+\beta\bar L_f$, as in (64) and in the display before it.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 30, proof of Theorem 15, last two displays

import Mathlib
import Definitions.Def_NecoaraNG_FDM_Setting

namespace NecoaraNG.FDM

open scoped InnerProductSpace

/-- Proof of Theorem 15, last display, p. 30: one step of (FDM) contracts the optimality gap,
`f(x^{k+1}) - f* ≤ 1 / (1 + L κ / (4 (L_f + L̄_f + β L̄_f)²)) · (f(x^k) - f*)`, with `f* = f x*`. -/
theorem one_step {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ)
    (β L Lbar : ℝ) (hβ : 0 < β) (hLpos : 0 < L) (hLbar : 0 < Lbar)
    (α : ℕ → ℝ) (e x : ℕ → NecoaraNG.Chain.E n) (hrun : IsFDMRun X f β L Lbar α e x) :
    ∀ k : ℕ, f (x (k + 1)) - f xstar ≤
      1 / (1 + L * κ / (4 * (Lf + Lbar + β * Lbar) ^ 2)) * (f (x k) - f xstar) := by sorry

end NecoaraNG.FDM
