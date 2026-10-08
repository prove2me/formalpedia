-- Prove2me | Theorems.Thm_NonuniformKuramoto_PhaseSync_theorem_V_10_part1
-- name    : NonuniformKuramoto.PhaseSync.theorem_V_10_part1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:21:45.036134+00:00
-- url     : https://prove2.me/theorems/795e6482-6bcd-4225-b6b3-a57a00710974
-- title:
--   Theorem V.10 1), p. 27 — the phases synchronize exponentially to θ_∞(t) ∈ [θ_min(0), θ_max(0)] + ω̄t
-- statement:
--   Consider the non-uniform Kuramoto model with $n \ge 2$ oscillators, $D_i > 0$, $P_{ij} \ge 0$ for $i \ne j$, $P_{ii} = 0$, where the graph induced by $P$ has a globally reachable node, all phase shifts vanish ($\varphi_{\max} = 0$), and $\omega_i/D_i = \bar\omega$ for all $i$. Let $\gamma \in [0,\pi[$ and let $\theta(t)$ be a solution on $[0,\infty)$ with $\theta(0) \in \bar\Delta(\gamma)$. Then there is a constant $c \in [\theta_{\min}(0), \theta_{\max}(0)]$ such that the phases synchronize exponentially to $\theta_\infty(t) = c + \bar\omega t$: there are $C \in \mathbb R$ and $\lambda > 0$ with
--
--   $$|\theta_i(t) - (c + \bar\omega t)| \le C\,e^{-\lambda t} \qquad \text{for all } i \text{ and all } t \ge 0 .$$
--
--   This is the general (possibly non-symmetric) phase-synchronization statement; statement 2) of Theorem V.10 sharpens it under symmetric coupling.
--
--   **Formalization Note** $\theta_{\min}(0)$, $\theta_{\max}(0)$ and the conclusion refer to the initial real lift with spread at most $\gamma$ and to the same continuous lifted trajectory. $n \ge 2$ and $P_{ii} = 0$ are the paper's standing conventions.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, pp. 26–27, Theorem V.10 1)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model

namespace NonuniformKuramoto.PhaseSync

/-- Theorem V.10 1) (Dörfler–Bullo, arXiv:0910.5673v4, pp. 26–27): if the graph induced by `P`
has a globally reachable node, `ϕ_max = 0` and `ωᵢ/Dᵢ = ω̄` for all `i`, then for every
`θ(0) ∈ ∆̄(γ)` with `γ ∈ [0, π[` the phases synchronize exponentially to
`θ_∞(t) = c + ω̄ t` for some `c ∈ [θ_min(0), θ_max(0)]`. -/
theorem theorem_V_10_part1 {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (ωbar : ℝ)
    (hn : 2 ≤ n) (hD : ∀ i, 0 < D i) (hP : ∀ i j, i ≠ j → 0 ≤ P i j)
    (hPii : ∀ i, P i i = 0) (hϕ : ∀ i j, ϕ i j = 0) (hω : ∀ i, ω i / D i = ωbar)
    (hreach : NonuniformKuramoto.CondI.HasGloballyReachableNode P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγπ : γ < Real.pi)
    (θ : ℝ → Fin n → ℝ) (hsol : NonuniformKuramoto.CondI.IsSolution D ω P ϕ θ) (h0 : NonuniformKuramoto.CondI.ArcClosed γ (θ 0)) :
    ∃ c : ℝ, (∃ i, θ 0 i ≤ c) ∧ (∃ i, c ≤ θ 0 i) ∧
      ∃ C κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 0 ≤ t → ∀ i,
        |θ t i - (c + ωbar * t)| ≤ C * Real.exp (-κ * t) := by sorry

end NonuniformKuramoto.PhaseSync
