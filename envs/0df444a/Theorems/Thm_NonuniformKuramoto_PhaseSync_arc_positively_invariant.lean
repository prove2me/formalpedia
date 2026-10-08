-- Prove2me | Theorems.Thm_NonuniformKuramoto_PhaseSync_arc_positively_invariant
-- name    : NonuniformKuramoto.PhaseSync.arc_positively_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:21:45.460176+00:00
-- url     : https://prove2.me/theorems/37ec686a-3b45-4007-94b0-2362b448ffad
-- title:
--   Proof of Theorem V.10, p. 27 — ∆̄(γ) is positively invariant for every γ ∈ [0, π[
-- statement:
--   Consider the non-uniform Kuramoto model with $n \ge 2$ oscillators, $D_i > 0$, $P_{ij} \ge 0$ for $i \ne j$, $P_{ii} = 0$, a globally reachable node in the graph induced by $P$, zero phase shifts $\varphi_{ij} = 0$, and $\omega_i / D_i = \bar\omega$ for all $i$. Let $\gamma \in [0,\pi[$. Then $\bar\Delta(\gamma)$ is positively invariant: for every solution $\theta(t)$ on $[0,\infty)$,
--
--   $$\theta_i(0) - \theta_j(0) \le \gamma \ \ \forall i,j \quad\Longrightarrow\quad \theta_i(t) - \theta_j(t) \le \gamma \ \ \forall i,j,\ \forall t \ge 0 .$$
--
--   This is the phase-cohesiveness step of Theorem V.10: it keeps all pairwise angle differences in $[-\gamma,\gamma] \subset\, ]-\pi,\pi[$, where the coupling acts as a contraction.
--
--   **Formalization Note** Stated on a real lift: the hypothesis is for the initial lift and the conclusion for the same continuous lifted trajectory. The globally reachable node and $n \ge 2$ are hypotheses of Theorem V.10 under which the paper proves this step; they are kept although the step does not need them.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 27, proof of Theorem V.10

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model

namespace NonuniformKuramoto.PhaseSync

/-- Proof of Theorem V.10, p. 27: under the hypotheses of Theorem V.10, for every
`γ ∈ [0, π[` the set `∆̄(γ)` is positively invariant: every solution of (8) starting in
`∆̄(γ)` (on a lift) stays in `∆̄(γ)` (on the same continuous lift) for all `t ≥ 0`. -/
theorem arc_positively_invariant {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (ωbar : ℝ)
    (hn : 2 ≤ n) (hD : ∀ i, 0 < D i) (hP : ∀ i j, i ≠ j → 0 ≤ P i j)
    (hPii : ∀ i, P i i = 0) (hϕ : ∀ i j, ϕ i j = 0) (hω : ∀ i, ω i / D i = ωbar)
    (hreach : NonuniformKuramoto.CondI.HasGloballyReachableNode P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγπ : γ < Real.pi)
    (θ : ℝ → Fin n → ℝ) (hsol : NonuniformKuramoto.CondI.IsSolution D ω P ϕ θ) (h0 : NonuniformKuramoto.CondI.ArcClosed γ (θ 0)) :
    ∀ t : ℝ, 0 ≤ t → NonuniformKuramoto.CondI.ArcClosed γ (θ t) := by sorry

end NonuniformKuramoto.PhaseSync
