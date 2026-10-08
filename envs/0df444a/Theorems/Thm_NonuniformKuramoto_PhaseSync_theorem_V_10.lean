-- Prove2me | Theorems.Thm_NonuniformKuramoto_PhaseSync_theorem_V_10
-- name    : NonuniformKuramoto.PhaseSync.theorem_V_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:24.892412+00:00
-- url     : https://prove2.me/theorems/84ff6687-6566-4012-9c7e-cda76256d4e3
-- title:
--   Theorem V.10 (Phase synchronization) — identical ω_i/D_i and ϕ_max = 0 give exponential phase synchronization from ∆̄(γ), γ ∈ [0, π[
-- statement:
--   Consider the non-uniform Kuramoto model
--
--   $$D_i\,\dot\theta_i = \omega_i - \sum_{j=1}^n P_{ij}\sin(\theta_i - \theta_j + \varphi_{ij}), \qquad i \in \{1,\dots,n\},$$
--
--   with $n \ge 2$, $D_i > 0$, $P_{ij} \ge 0$ for $i \ne j$ and $P_{ii} = 0$, where the graph induced by $P$ has a globally reachable node, all phase shifts vanish ($\varphi_{\max} = 0$), and $\omega_i/D_i = \bar\omega$ for all $i$. Let $\gamma \in [0,\pi[$ and let $\theta(t)$ be a solution on $[0,\infty)$ with $\theta(0) \in \bar\Delta(\gamma)$, that is, $\theta_i(0) - \theta_j(0) \le \gamma$ for all $i, j$. Then:
--
--   1. the phases synchronize exponentially to $\theta_\infty(t) = c + \bar\omega t$ for some $c \in [\theta_{\min}(0), \theta_{\max}(0)]$: there are $C$ and $\lambda > 0$ with $|\theta_i(t) - \theta_\infty(t)| \le C e^{-\lambda t}$ for all $i$ and $t \ge 0$;
--   2. if $P = P^T$, the phases synchronize exponentially to the weighted mean angle $\theta_\infty(t) = \sum_i D_i\theta_i(0)/\sum_i D_i + \bar\omega t$, and the disagreement $\delta(t) = \theta(t) - \theta_\infty(t)\mathbf 1$ satisfies
--
--   $$\|\delta(t)\|_2 \le \sqrt{D_{\max}/D_{\min}}\;\|\delta(0)\|_2\; e^{-\lambda_{\mathrm{ps}} t}, \qquad t \ge 0,$$
--
--   with the rate
--
--   $$\lambda_{\mathrm{ps}} = \lambda_2(L(P_{ij}))\,\mathrm{sinc}(\gamma)\,\cos(\angle(D\mathbf 1,\mathbf 1))^2 / D_{\max} .$$
--
--   For identical natural frequencies and lossless coupling this is the phase-synchronization counterpart of the paper's frequency-synchronization results, with an explicit worst-case rate expressed through the algebraic connectivity of the coupling graph.
--
--   **Formalization Note** (i) The paper prints (42) with a leading minus sign; the rate is a decay exponent and is stated as the positive number above. (ii) The page says only "a rate no worse than $\lambda_{\mathrm{ps}}$"; the proof refers to the proof of Theorem V.1 2), which yields the bound with the constant $\sqrt{D_{\max}/D_{\min}}$ (p. 19), and that bound is what is stated, together with exponential convergence in the sense of statement 1). (iii) Angles are real lifts: the hypothesis is on an initial lift with spread at most $\gamma$, and $\theta_{\min}(0)$, $\theta_{\max}(0)$, the weighted mean (well defined only on such a lift, footnote 3) and the conclusions refer to that lift and the same continuous trajectory. (iv) $n \ge 2$ and $P_{ii} = 0$ are the paper's conventions; $\varphi_{\max} = 0$ is written as $\varphi_{ij} = 0$ for all $i,j$, which is equivalent because $\varphi_{ij} \ge 0$.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, pp. 26–27, Theorem V.10 and (42); proof pattern p. 19 (proof of Theorem V.1 2))

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_PhaseSync_Rate

namespace NonuniformKuramoto.PhaseSync

/-- Theorem V.10 (Phase synchronization) (Dörfler–Bullo, arXiv:0910.5673v4, pp. 26–27).
Consider the non-uniform Kuramoto model (8) where the graph induced by `P` has a globally
reachable node, `ϕ_max = 0` and `ωᵢ/Dᵢ = ω̄` for all `i`. Then for every `θ(0) ∈ ∆̄(γ)`
with `γ ∈ [0, π[`:
1) the phases synchronize exponentially to `θ_∞(t) = c + ω̄ t` with `c ∈ [θ_min(0), θ_max(0)]`;
2) if `P = Pᵀ`, the phases synchronize exponentially to the weighted mean angle
   `θ_∞(t) = ∑ᵢ Dᵢθᵢ(0)/∑ᵢ Dᵢ + ω̄ t`, and the disagreement `δ(t) = θ(t) − θ_∞(t)𝟏` satisfies
   `‖δ(t)‖₂ ≤ √(D_max/D_min) ‖δ(0)‖₂ e^{−λ_ps t}` with the rate (42) taken positive. -/
theorem theorem_V_10 {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (ωbar : ℝ)
    (hn : 2 ≤ n) (hD : ∀ i, 0 < D i) (hP : ∀ i j, i ≠ j → 0 ≤ P i j)
    (hPii : ∀ i, P i i = 0) (hϕ : ∀ i j, ϕ i j = 0) (hω : ∀ i, ω i / D i = ωbar)
    (hreach : NonuniformKuramoto.CondI.HasGloballyReachableNode P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγπ : γ < Real.pi)
    (θ : ℝ → Fin n → ℝ) (hsol : NonuniformKuramoto.CondI.IsSolution D ω P ϕ θ) (h0 : NonuniformKuramoto.CondI.ArcClosed γ (θ 0)) :
    (∃ c : ℝ, (∃ i, θ 0 i ≤ c) ∧ (∃ i, c ≤ θ 0 i) ∧
      ∃ C κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 0 ≤ t → ∀ i,
        |θ t i - (c + ωbar * t)| ≤ C * Real.exp (-κ * t)) ∧
    ((∀ i j, P i j = P j i) →
      (∃ C κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 0 ≤ t → ∀ i,
        |θ t i - ((∑ k, D k * θ 0 k) / (∑ k, D k) + ωbar * t)| ≤ C * Real.exp (-κ * t)) ∧
      ∀ t : ℝ, 0 ≤ t →
        NonuniformKuramoto.CondI.norm2 (fun i => θ t i - ((∑ k, D k * θ 0 k) / (∑ k, D k) + ωbar * t))
          ≤ Real.sqrt (NonuniformKuramoto.CondII.Dmax D / Dmin D)
            * NonuniformKuramoto.CondI.norm2 (fun i => θ 0 i - (∑ k, D k * θ 0 k) / (∑ k, D k))
            * Real.exp (-lambdaPS D P γ * t)) := by sorry

end NonuniformKuramoto.PhaseSync
