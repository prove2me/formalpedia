-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondII_eq_37
-- name    : NonuniformKuramoto.CondII.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:26:05.441991+00:00
-- url     : https://prove2.me/theorems/4e128296-c000-4a13-9806-f062adb9f83f
-- title:
--   (37), p. 25 — Ẇ(Hθ) ≤ ‖Hθ‖₂ max{D_iD_j}(‖HD⁻¹ω‖₂ + X̃) − (κ/n) sinc(ρ) λ₂(L(P_ij cos φ_ij)) ‖Hθ‖₂²
-- statement:
--   Assume the standing assumptions of §V.B for the non-uniform Kuramoto model (8): $n\ge2$, $D_i>0$, $P=P^T$ with $P_{ij}\ge0$ inducing a connected graph, $\varphi_{ij}=\varphi_{ji}\in[0,\pi/2[$ for $i\ne j$, $P_{ii}=\varphi_{ii}=0$. Let $\rho\in\,]0,\pi[$ and $\theta\in\Delta(\pi)$ with $\|H\theta\|_2\le\rho$. Then the derivative $\dot W(H\theta)=(H\theta)^T\operatorname{diag}(D_iD_j)H\dot\theta$ of the Lyapunov function (34) along (8) satisfies
--   $$
--   \dot W(H\theta)\le\|H\theta\|_2\max_{i\ne j}\{D_iD_j\}\big(\|HD^{-1}\omega\|_2+\tilde X\big)-(\kappa/n)\operatorname{sinc}(\rho)\,\lambda_2(L(P_{ij}\cos(\varphi_{ij})))\,\|H\theta\|_2^2 .\tag{37}
--   $$
--
--   The right-hand side is negative once $\|H\theta\|_2$ exceeds an explicit threshold; this is the dissipation inequality behind the ultimate boundedness of the phase differences.
--
--   **Formalization Note** The bound is pointwise in the configuration: $\dot\theta$ is the right-hand side of (8) at $\theta$, not the derivative of a trajectory. $\varphi_{ij}=\varphi_{ji}$ is a disclosed reading of the page (see the model definition).
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 25, (37)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace NonuniformKuramoto.CondII

/-- Inequality (37) (Dörfler–Bullo, arXiv:0910.5673v4, p. 25): for `ρ ∈ ]0, π[` and every
`θ ∈ ∆(π)` with `‖Hθ‖₂ ≤ ρ`, the derivative of `W(Hθ)` along (8) satisfies
`Ẇ(Hθ) ≤ ‖Hθ‖₂ max_{i≠j}{D_iD_j} (‖HD⁻¹ω‖₂ + X̃) − (κ/n) sinc(ρ) λ₂(L(P_ij cos ϕ_ij)) ‖Hθ‖₂²`. -/
theorem eq_37 {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hyp : StandingHyp D P ϕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi) (θ : Fin n → ℝ)
    (hθ : NonuniformKuramoto.CondI.ArcOpen Real.pi θ) (hθρ : normH θ ≤ ρ) :
    Wdot D ω P ϕ θ ≤
      normH θ * maxDD D * (normH (fun i => ω i / D i) + Xtilde D P ϕ) -
        kappa D / n * Real.sinc ρ * lambda2 (lossless P ϕ) * normH θ ^ 2 := by sorry

end NonuniformKuramoto.CondII
