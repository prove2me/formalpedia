-- Prove2me | Theorems.Thm_NecoaraNG_FGM_fgm_estimate
-- name    : NecoaraNG.FGM.fgm_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:33.684483+00:00
-- url     : https://prove2.me/theorems/c90fa93d-ddd9-494f-a34d-a785fa40c3d7
-- title:
--   Proof of Theorem 14, pp. 25–26 — (FGM) with β = (√L_f − √κ_f)/(√L_f + √κ_f) satisfies φ*_k ≥ f(x^k) for α_k = √μ_f
-- statement:
--   Let $X$, $f$, $L_f$, $\kappa$ be as in Theorem 14 and let $(x^k, y^k)$ be a run of the fast gradient method (FGM) with constant parameter
--   $$\beta = \frac{\sqrt{L_f} - \sqrt{\kappa}}{\sqrt{L_f} + \sqrt{\kappa}},$$
--   whose points $y^k$ all have the same nearest point $y^*$ in $X^*$. Let $\phi_k$ be the estimate functions (55) with the constant choice $\alpha_k = \sqrt{\mu_f}$, $\mu_f = \kappa / L_f$. Then for every $k \ge 0$
--   $$f(x^k) \le \phi_k(z) \qquad \text{for all } z \in \mathbb{R}^n,$$
--   that is, $f(x^k) \le \phi_k^*$: the FGM iterates satisfy condition (58) of Lemma 2.
--
--   This is the step of the proof of Theorem 14 that connects the algorithm to the estimate sequence.
--
--   **Formalization Note** Smoothness, convexity and (10) are assumed on $\mathbb{R}^n$, because the argument evaluates the gradient-mapping inequality (29) at the extrapolated points $y^k$, which may lie outside $X$. The same-projection hypothesis is that of Theorem 14; the page's argument for this step does not use it.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, pp. 25–26, proof of Theorem 14 (claim φ*_k ≥ f(x^k))

import Mathlib
import Definitions.Def_NecoaraNG_FGM_Setting

namespace NecoaraNG.FGM

open scoped InnerProductSpace

/-- Proof of Theorem 14, pp. 25–26: the iterates of (FGM) with
`β = (√L_f - √κ)/(√L_f + √κ)` satisfy (58) for the estimate functions (55) with constant
`α_k = √μ_f = √(κ/L_f)`: `f(x^k) ≤ φ_k(z)` for every `k ≥ 0` and every `z ∈ ℝⁿ`. -/
theorem fgm_estimate {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : NecoaraNG.Chain.E n → ℝ) (hdiff : ∀ x, DifferentiableAt ℝ f x) (hf : ConvexOn ℝ Set.univ f)
    (Lf : ℝ) (hLf : 0 < Lf) (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet X f)
    (κ : ℝ) (hκ : 0 < κ) (hqs : QuasiStrongEverywhere X f κ)
    (x y : ℕ → NecoaraNG.Chain.E n)
    (hrun : IsFGMRun X f Lf ((Real.sqrt Lf - Real.sqrt κ) / (Real.sqrt Lf + Real.sqrt κ)) x y)
    (ystar : NecoaraNG.Chain.E n) (hsame : ∀ k, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) (y k) ystar) :
    ∀ k : ℕ, ∀ z, f (x k) ≤ phi f Lf κ (fun _ => Real.sqrt (κ / Lf)) x y k z := by sorry

end NecoaraNG.FGM
