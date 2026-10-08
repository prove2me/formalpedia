-- Prove2me | Theorems.Thm_NonuniformKuramoto_PhaseSync_rotating_frame_consensus
-- name    : NonuniformKuramoto.PhaseSync.rotating_frame_consensus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:21:35.25813+00:00
-- url     : https://prove2.me/theorems/9dfa6454-21cb-41a5-99e2-05bedcbd0578
-- title:
--   (43), p. 27 — in the rotating frame θ ↦ θ − ω̄t the model is the consensus protocol θ̇_i = −Σ_j a_ij(t)(θ_i − θ_j), a_ij(t) > 0
-- statement:
--   Under the hypotheses of Theorem V.10 ($n \ge 2$, $D_i > 0$, $P_{ij} \ge 0$ for $i \ne j$, $P_{ii} = 0$, a globally reachable node, $\varphi_{ij} = 0$, $\omega_i/D_i = \bar\omega$), let $\gamma \in [0,\pi[$ and let $\theta(t)$ be a solution on $[0,\infty)$ with $\theta(0) \in \bar\Delta(\gamma)$. Define the time-varying weights
--
--   $$a_{ij}(t) = \frac{P_{ij}}{D_i}\,\mathrm{sinc}\big(\theta_i(t) - \theta_j(t)\big) .$$
--
--   Then:
--
--   1. $a_{ij}(t) > 0$ for every $t \ge 0$ and every pair with $P_{ij} > 0$;
--   2. in the rotating frame $\psi(t) = \theta(t) - \bar\omega t\,\mathbf 1$ the dynamics is the time-varying consensus protocol
--
--   $$\dot\psi_i(t) = -\sum_{j=1}^n a_{ij}(t)\big(\psi_i(t) - \psi_j(t)\big), \qquad t \ge 0 .$$
--
--   This rewrites phase synchronization of the oscillators as consensus of a linear time-varying system whose weights stay positive on the edges of the coupling graph.
--
--   **Formalization Note** The page says $a_{ij}(t)$ is strictly positive; this holds exactly on the edges ($P_{ij} > 0$), since $a_{ij} = 0$ where $P_{ij} = 0$, and is stated so. The derivative in item 2 is taken within $[0,\infty)$, as for solutions.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 27, (43)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model

namespace NonuniformKuramoto.PhaseSync

/-- (43), p. 27: under the hypotheses of Theorem V.10, for a solution starting in `∆̄(γ)`,
`γ ∈ [0, π[`, the weights `aᵢⱼ(t) = (Pᵢⱼ/Dᵢ) sinc(θᵢ(t) − θⱼ(t))` are strictly positive on
every edge (`Pᵢⱼ > 0`), and in the rotating frame `ψ(t) = θ(t) − ω̄ t 𝟏` the model is the
time-varying consensus protocol `ψ̇ᵢ(t) = −∑ⱼ aᵢⱼ(t)(ψᵢ(t) − ψⱼ(t))`. -/
theorem rotating_frame_consensus {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (ωbar : ℝ)
    (hn : 2 ≤ n) (hD : ∀ i, 0 < D i) (hP : ∀ i j, i ≠ j → 0 ≤ P i j)
    (hPii : ∀ i, P i i = 0) (hϕ : ∀ i j, ϕ i j = 0) (hω : ∀ i, ω i / D i = ωbar)
    (hreach : NonuniformKuramoto.CondI.HasGloballyReachableNode P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγπ : γ < Real.pi)
    (θ : ℝ → Fin n → ℝ) (hsol : NonuniformKuramoto.CondI.IsSolution D ω P ϕ θ) (h0 : NonuniformKuramoto.CondI.ArcClosed γ (θ 0)) :
    (∀ t : ℝ, 0 ≤ t → ∀ i j, 0 < P i j → 0 < P i j / D i * Real.sinc (θ t i - θ t j)) ∧
    (∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (fun s : ℝ => fun i => θ s i - ωbar * s)
        (fun i => -∑ j, (P i j / D i * Real.sinc (θ t i - θ t j)) *
          ((θ t i - ωbar * t) - (θ t j - ωbar * t)))
        (Set.Ici 0) t) := by sorry

end NonuniformKuramoto.PhaseSync
