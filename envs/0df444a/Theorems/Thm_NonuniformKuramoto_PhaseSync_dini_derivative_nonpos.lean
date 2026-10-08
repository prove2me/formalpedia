-- Prove2me | Theorems.Thm_NonuniformKuramoto_PhaseSync_dini_derivative_nonpos
-- name    : NonuniformKuramoto.PhaseSync.dini_derivative_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:21:42.252125+00:00
-- url     : https://prove2.me/theorems/9742375c-4900-4e09-a39e-c87f76333d7a
-- title:
--   Proof of Theorem V.10, p. 27 — D⁺V = −Σ_k((P_mk/D_m) sin(θ_m − θ_k) + (P_ℓk/D_ℓ) sin(θ_k − θ_ℓ)) ≤ 0
-- statement:
--   Consider the non-uniform Kuramoto model with $D_i > 0$, $P_{ij} \ge 0$ for $i \ne j$, $P_{ii} = 0$, zero phase shifts $\varphi_{ij} = 0$, and natural frequencies proportional to the damping, $\omega_i / D_i = \bar\omega$ for all $i$. Let $\gamma \in [0,\pi[$ and let $\theta \in \mathbb R^n$ be a configuration with $\theta_i - \theta_j \le \gamma$ for all $i,j$ (a lift of a point of $\bar\Delta(\gamma)$). Let $m$ and $\ell$ be indices of a largest and a smallest coordinate, $\theta_\ell \le \theta_k \le \theta_m$ for all $k$. Then, writing $f$ for the vector field of the model,
--
--   $$f_m(\theta) - f_\ell(\theta) = -\sum_{k=1}^n \Big(\frac{P_{mk}}{D_m}\sin(\theta_m-\theta_k) + \frac{P_{\ell k}}{D_\ell}\sin(\theta_k-\theta_\ell)\Big) \le 0 .$$
--
--   The left-hand side is the upper Dini derivative of the arc length $V(\theta) = \theta_m - \theta_\ell$ along the flow (for the extremal indices realizing it), so this is the pointwise estimate behind the positive invariance of $\bar\Delta(\gamma)$.
--
--   **Formalization Note** "Both sinusoidal terms are positive" on the page means nonnegative: the terms vanish for $k \in \{m,\ell\}$ and wherever $P_{mk} = 0$ or $P_{\ell k} = 0$. The statement is pointwise in $\theta$; the Dini derivative itself does not appear.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 27, proof of Theorem V.10, first display; p. 21, V, m and ℓ

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model

namespace NonuniformKuramoto.PhaseSync

/-- Proof of Theorem V.10, p. 27: with `ϕ_max = 0` and `ωᵢ/Dᵢ = ω̄`, at a configuration in
`∆̄(γ)`, `γ ∈ [0, π[`, whose counterclockwise maximum and minimum are `θ_m` and `θ_ℓ`,
`θ̇_m − θ̇_ℓ = −∑ₖ ((P_mk/D_m) sin(θ_m − θ_k) + (P_ℓk/D_ℓ) sin(θ_k − θ_ℓ)) ≤ 0`. -/
theorem dini_derivative_nonpos {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (ωbar : ℝ)
    (hn : 2 ≤ n) (hD : ∀ i, 0 < D i) (hP : ∀ i j, i ≠ j → 0 ≤ P i j)
    (hPii : ∀ i, P i i = 0) (hϕ : ∀ i j, ϕ i j = 0) (hω : ∀ i, ω i / D i = ωbar)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγπ : γ < Real.pi) (θ : Fin n → ℝ) (hθ : NonuniformKuramoto.CondI.ArcClosed γ θ)
    (m ℓ : Fin n) (hm : ∀ k, θ k ≤ θ m) (hℓ : ∀ k, θ ℓ ≤ θ k) :
    NonuniformKuramoto.CondI.field D ω P ϕ θ m - NonuniformKuramoto.CondI.field D ω P ϕ θ ℓ
        = -∑ k, (P m k / D m * Real.sin (θ m - θ k) + P ℓ k / D ℓ * Real.sin (θ k - θ ℓ)) ∧
      NonuniformKuramoto.CondI.field D ω P ϕ θ m - NonuniformKuramoto.CondI.field D ω P ϕ θ ℓ ≤ 0 := by sorry

end NonuniformKuramoto.PhaseSync
