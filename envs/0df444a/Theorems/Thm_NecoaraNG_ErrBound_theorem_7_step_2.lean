-- Prove2me | Theorems.Thm_NecoaraNG_ErrBound_theorem_7_step_2
-- name    : NecoaraNG.ErrBound.theorem_7_step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:54.724231+00:00
-- url     : https://prove2.me/theorems/d11013b8-d9de-4dcb-9366-49b85798a438
-- title:
--   Proof of Theorem 7, p. 12 — ‖g(x)‖ ≥ (√(L_f(κ_f + L_f)) − L_f) ‖x⁺ − x̄⁺‖
-- statement:
--   Under the standing assumptions of problem (P) ($X\subseteq\mathbb R^n$ closed and convex, $f$ convex on $X$ and differentiable at every point of $X$, $\nabla f$ Lipschitz on $X$ with constant $L_f>0$, an optimal solution exists), suppose $f$ has quadratic functional growth (22) with constant $\kappa_f>0$. Let $x\in X$, let $x^+=[x-\tfrac1{L_f}\nabla f(x)]_X$, $g(x)=L_f(x-x^+)$, and let $\bar x^+=[x^+]_{X^*}$. Then
--   $$
--   \|g(x)\|\ \ge\ \Bigl(\sqrt{L_f(\kappa_f+L_f)}-L_f\Bigr)\,\|x^+-\bar x^+\| .
--   $$
--
--   This is the intermediate error bound at the point $x^+$ obtained in the proof of Theorem 7; the theorem then transfers it from $x^+$ back to $x$.
--
--   **Formalization Note** The factor $\sqrt{L_f(\kappa_f+L_f)}-L_f$ is positive because $\kappa_f>0$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 12, proof of Theorem 7, display after "We conclude that"

import Mathlib
import Definitions.Def_NecoaraNG_ErrBound_Setting

open scoped InnerProductSpace

namespace NecoaraNG.ErrBound

theorem theorem_7_step_2 {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hf : ConvexOn ℝ X f) (hdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (Lf : ℝ) (hLf : 0 < Lf)
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hF : NecoaraNG.Chain.QuadFunGrowth X f κ) :
    ∀ x ∈ X, ∀ xp, IsPGStep X f Lf x xp → ∀ xpbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) xp xpbar →
      (Real.sqrt (Lf * (κ + Lf)) - Lf) * ‖xp - xpbar‖ ≤ ‖Lf • (x - xp)‖ := by sorry

end NecoaraNG.ErrBound
