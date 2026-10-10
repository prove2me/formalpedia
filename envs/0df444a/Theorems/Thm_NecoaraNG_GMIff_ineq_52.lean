-- Prove2me | Theorems.Thm_NecoaraNG_GMIff_ineq_52
-- name    : NecoaraNG.GMIff.ineq_52
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:39.930299+00:00
-- url     : https://prove2.me/theorems/5cad7d67-fdff-4a06-a0c4-b5807e61db5b
-- title:
--   (52), p. 22 — under (22), ‖x^{k+1} − x̄^{k+1}‖² ≤ (1/(1 + κ_f α_k))‖x^k − x̄^k‖²
-- statement:
--   Under the standing assumptions of problem (P) ($X$ nonempty closed convex, $f$ convex with $L_f$-Lipschitz gradient (1) on $X$, $L_f > 0$, $X^* \ne \emptyset$), suppose $f$ has quadratic functional growth (22) with constant $\kappa_f > 0$. Let $0 < \alpha_k \le 1/L_f$, $x^k \in X$ and $x^{k+1} = [x^k - \alpha_k \nabla f(x^k)]_X$, and let $\bar x^k = [x^k]_{X^*}$, $\bar x^{k+1} = [x^{k+1}]_{X^*}$. Then
--   $$\|x^{k+1} - \bar x^{k+1}\|^2 \le \frac{1}{1 + \kappa_f \alpha_k}\,\|x^k - \bar x^k\|^2 .$$
--
--   This is the one-step contraction of the squared distance to the optimal set; it is the "if" half of Theorem 13 and, iterated, gives Theorem 12.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 22, proof of Theorem 12, (52)

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

namespace NecoaraNG.GMIff

theorem ineq_52 (n : ℕ) (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1 / Lf) :
    ∀ xk ∈ X, ∀ xk1, NecoaraNG.Chain.IsNearest X (xk - α • gradient f xk) xk1 →
      ∀ xkbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xk xkbar →
      ∀ xk1bar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xk1 xk1bar →
        ‖xk1 - xk1bar‖ ^ 2 ≤ 1 / (1 + κ * α) * ‖xk - xkbar‖ ^ 2 := by sorry

end NecoaraNG.GMIff
