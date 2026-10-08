-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondII_sinc_bound
-- name    : NonuniformKuramoto.CondII.sinc_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:36.471234+00:00
-- url     : https://prove2.me/theorems/d70fbdd8-47bc-4205-90b1-5c7be5127327
-- title:
--   Proof of Theorem V.5, p. 25 — on S(ρ): |θᵢ − θⱼ| ≤ ‖Hθ‖₂ ≤ ρ, 1 ≥ sinc(θᵢ − θⱼ) ≥ sinc(ρ), (θᵢ − θⱼ)sin(θᵢ − θⱼ) ≥ (θᵢ − θⱼ)² sinc(ρ)
-- statement:
--   Let $\rho\in\,]0,\pi[$ and let $\theta$ be a configuration in $\mathcal S(\rho)=\{\theta\in\Delta(\pi):\|H\theta\|_2\le\rho\}$. Then for all $i,j$,
--   $$
--   |\theta_i-\theta_j|\le\|H\theta\|_2\le\rho,\qquad 1\ge\operatorname{sinc}(\theta_i-\theta_j)\ge\operatorname{sinc}(\rho),\qquad (\theta_i-\theta_j)\sin(\theta_i-\theta_j)\ge(\theta_i-\theta_j)^2\operatorname{sinc}(\rho),
--   $$
--   where $\operatorname{sinc}(x)=\sin(x)/x$ and $\operatorname{sinc}(0)=1$.
--
--   This is the step that turns the sinusoidal coupling of (35) into a quadratic form, so that the algebraic connectivity can be used.
--
--   **Formalization Note** $\operatorname{sinc}$ is Mathlib's `Real.sinc`, equal to $1$ at $0$. The first inequality is the page's "$\|H\theta\|_\infty\le\|H\theta\|_2$", so $\theta\in\bar\Delta(\rho)$.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 25, Proof of Theorem V.5, first paragraph

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace NonuniformKuramoto.CondII

/-- Proof of Theorem V.5 (Dörfler–Bullo, arXiv:0910.5673v4, p. 25): for `θ ∈ S(ρ) = {θ ∈ ∆(π) :
‖Hθ‖₂ ≤ ρ}`, `ρ ∈ ]0, π[`, every difference satisfies `|θ_i − θ_j| ≤ ‖Hθ‖₂ ≤ ρ` (so `θ ∈ ∆̄(ρ)`),
`1 ≥ sinc(θ_i − θ_j) ≥ sinc(ρ)` and `(θ_i − θ_j) sin(θ_i − θ_j) ≥ (θ_i − θ_j)² sinc(ρ)`. -/
theorem sinc_bound {n : ℕ} (ρ : ℝ) (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi) (θ : Fin n → ℝ)
    (hθ : NonuniformKuramoto.CondI.ArcOpen Real.pi θ) (hθρ : normH θ ≤ ρ) (i j : Fin n) :
    |θ i - θ j| ≤ normH θ ∧ |θ i - θ j| ≤ ρ ∧
      Real.sinc (θ i - θ j) ≤ 1 ∧ Real.sinc ρ ≤ Real.sinc (θ i - θ j) ∧
      (θ i - θ j) ^ 2 * Real.sinc ρ ≤ (θ i - θ j) * Real.sin (θ i - θ j) := by sorry

end NonuniformKuramoto.CondII
