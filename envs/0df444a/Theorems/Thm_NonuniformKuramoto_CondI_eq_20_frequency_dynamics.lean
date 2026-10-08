-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondI_eq_20_frequency_dynamics
-- name    : NonuniformKuramoto.CondI.eq_20_frequency_dynamics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:15.969248+00:00
-- url     : https://prove2.me/theorems/26839ae9-b0ea-48f4-a391-be8385f2baa4
-- title:
--   (20) — frequency dynamics $\frac{d}{dt}D_i\dot\theta_i = -\sum_j P_{ij}\cos(\theta_i-\theta_j+\varphi_{ij})(\dot\theta_i-\dot\theta_j)$
-- statement:
--   Consider the non-uniform Kuramoto model (8) with $D_i>0$, $P_{ij}\ge0$, $\varphi_{ij}\in[0,\pi/2[$ for $i\ne j$ and $P_{ii}=\varphi_{ii}=0$. Let $\theta(t)$, $t\ge0$, be a solution and write $\dot\theta_i(t)$ for the right-hand side of (8) divided by $D_i$, evaluated at $\theta(t)$. Then for every $i$ and every $t\ge0$ the function $t\mapsto D_i\dot\theta_i(t)$ is differentiable (one-sidedly at $t=0$) and
--
--   $$\frac{d}{dt}D_i\dot\theta_i = -\sum_{j=1}^n P_{ij}\cos(\theta_i-\theta_j+\varphi_{ij})\,(\dot\theta_i-\dot\theta_j).$$
--
--   This identity shows that the frequencies obey a time-varying consensus protocol with state-dependent weights; it is the starting point of the proof of Theorem V.1.
--
--   **Formalization Note** The derivative is a derivative within $[0,\infty)$; $\dot\theta$ is the vector field of (8) along the solution.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 17, (20) (proof of Theorem V.1)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondI

/-- (20), p. 17: along every solution of (8), the weighted frequencies `D_i θ̇_i` evolve by
`d/dt (D_i θ̇_i) = −∑_j P_ij cos(θ_i − θ_j + ϕ_ij) (θ̇_i − θ̇_j)`, where `θ̇ = field … (θ t)`. -/
theorem eq_20_frequency_dynamics {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 ≤ P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (θ : ℝ → Fin n → ℝ) (hθ : IsSolution D ω P ϕ θ) (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => D i * field D ω P ϕ (θ s) i)
      (-∑ j, P i j * Real.cos (θ t i - θ t j + ϕ i j)
          * (field D ω P ϕ (θ t) i - field D ω P ϕ (θ t) j))
      (Set.Ici 0) t := by sorry

end NonuniformKuramoto.CondI
