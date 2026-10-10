-- Prove2me | Theorems.Thm_NecoaraNG_FGM_qfg_at_start
-- name    : NecoaraNG.FGM.qfg_at_start
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:21.641149+00:00
-- url     : https://prove2.me/theorems/cd6495b8-33d0-470d-a98f-a0eceeabde0a
-- title:
--   Proof of Theorem 14, p. 26 — κ_f/2 ‖x⁰ − x̄⁰‖² ≤ f(x⁰) − f* for x⁰ ∈ X
-- statement:
--   Let $X$, $f$, $L_f$, $\kappa$ be as in Theorem 14. For every feasible $x^0 \in X$ and every nearest point $\bar x^0 = [x^0]_{X^*}$,
--   $$\frac{\kappa}{2}\|x^0 - \bar x^0\|^2 \le f(x^0) - f^* .$$
--
--   This is quadratic functional growth (22) at a feasible point, the last ingredient of the proof of Theorem 14: it bounds the initial distance term of Lemma 2 by the initial gap.
--
--   **Formalization Note** $f^* = f(x^*)$ for a fixed minimizer $x^*$. The hypotheses are those of Theorem 14 (smoothness, convexity and (10) on $\mathbb{R}^n$); the statement only concerns $x^0 \in X$. The same implication (10) ⇒ (22) is posed in the companion missions I and IV of this series; it is posed again here because draft items cannot import each other.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 26, proof of Theorem 14 (last sentence)

import Mathlib
import Definitions.Def_NecoaraNG_FGM_Setting

namespace NecoaraNG.FGM

open scoped InnerProductSpace

/-- Proof of Theorem 14, p. 26: quadratic functional growth (22) at a feasible point,
`κ/2 ‖x⁰ - x̄⁰‖² ≤ f(x⁰) - f*` for `x⁰ ∈ X` and `x̄⁰ = [x⁰]_{X*}`. -/
theorem qfg_at_start {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x, DifferentiableAt ℝ f x) (hf : ConvexOn ℝ Set.univ f)
    (Lf : ℝ) (hLf : 0 < Lf) (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : QuasiStrongEverywhere X f κ) :
    ∀ x0 ∈ X, ∀ x0bar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x0 x0bar →
      κ / 2 * ‖x0 - x0bar‖ ^ 2 ≤ f x0 - f xstar := by sorry

end NecoaraNG.FGM
