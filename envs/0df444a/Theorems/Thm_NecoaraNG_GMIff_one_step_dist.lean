-- Prove2me | Theorems.Thm_NecoaraNG_GMIff_one_step_dist
-- name    : NecoaraNG.GMIff.one_step_dist
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:14.646631+00:00
-- url     : https://prove2.me/theorems/aa55b2ef-25e6-44cf-a92d-c0a4c6b4fdc4
-- title:
--   Proof of Theorem 12, p. 22 — ‖x^{k+1} − x‖² ≤ ‖x^k − x‖² − 2α_k(f(x^{k+1}) − f(x)) for all x ∈ X
-- statement:
--   Under the standing assumptions of problem (P) ($X$ nonempty closed convex, $f$ convex with $L_f$-Lipschitz gradient (1) on $X$, $L_f > 0$, $X^* \ne \emptyset$), let $0 < \alpha \le 1/L_f$, let $x^k \in X$ and let $x^{k+1} = [x^k - \alpha \nabla f(x^k)]_X$. Then
--   $$\|x^{k+1} - x\|^2 \le \|x^k - x\|^2 - 2\alpha\big(f(x^{k+1}) - f(x)\big) \qquad \forall x \in X .$$
--
--   This one-step inequality of the projected gradient method holds for every convex smooth objective; evaluated at $x = \bar x^k$ it drives the linear rate of Theorem 12 and the function-value rate (53).
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 22, proof of Theorem 12, display chain ending in ∀x ∈ X (uses (46), (47))

import Mathlib
import Definitions.Def_NecoaraNG_GMIff_Setting

namespace NecoaraNG.GMIff

theorem one_step_dist (n : ℕ) (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f)
    (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1 / Lf) :
    ∀ xk ∈ X, ∀ xk1, NecoaraNG.Chain.IsNearest X (xk - α • gradient f xk) xk1 →
      ∀ x ∈ X, ‖xk1 - x‖ ^ 2 ≤ ‖xk - x‖ ^ 2 - 2 * α * (f xk1 - f x) := by sorry

end NecoaraNG.GMIff
