-- Prove2me | Theorems.Thm_IteratedLP_Gaussian_corollary_3_2
-- name    : IteratedLP.Gaussian.corollary_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:21:35.303795+00:00
-- url     : https://prove2.me/theorems/e5c3be07-401d-4c64-9fb4-ea4aae18c4c5
-- title:
--   Corollary 3.2 — localization of optimizers by an auxiliary value gap
-- statement:
--   Consider a sequence of problems as in Theorem 3.1, indexed by $N$: dimensions $n_N,m_N$, nonempty compact $C_N\subset\mathbb R^{n_N}$, $D_N\subset\mathbb R^{m_N}$, payoffs $\psi_N$ continuous on $C_N\times D_N$, Gaussian inputs $(G,g,h)$, primary values $\Phi_N$, and nonempty deterministic compact sets $B_N\subset C_N$. Let $v\in\mathbb R$ and $\delta>0$.
--   1. (min–max) Let $\phi_{B_N}=\min_{w\in B_N}\max_{u\in D_N}\{\|w\|g^\top u+\|u\|h^\top w+\psi_N(w,u)\}$. If $\Phi_N\to v$ in probability and $\mathbb P(\phi_{B_N}\ge v+\delta)\to1$, then
--   $$\mathbb P(\text{some primary minimizer belongs to }B_N)\to0.$$
--   2. (max–min) For $\Phi_N=\max_{w\in C_N}\min_{u\in D_N}\{u^\top Gw+\psi_N(w,u)\}$ and $\phi_{B_N}=\max_{w\in B_N}\min_{u\in D_N}\{\|w\|g^\top u+\|u\|h^\top w+\psi_N(w,u)\}$: if $\Phi_N\to v$ in probability and $\mathbb P(\phi_{B_N}\le v-\delta)\to1$, then the probability that some primary maximizer belongs to $B_N$ tends to $0$.
--
--   The corollary turns a gap in the auxiliary problem restricted to a "bad" set into the statement that the optimizer of the primary problem avoids that set.
--
--   Differences from the source:
--
--   - generalization: part (ii): max–min problems with a fixed set D for the minimizing variable → the set D_N may depend on N (in both parts); reason: a constant sequence D_N = D is the source's case
--   - encoding: Φ_N → v in probability; with high probability no primary minimizer (maximizer) belongs to B_N → ∀ ε > 0, P(|Φ_N − v| > ε) → 0; the outer probability of {∃ w ∈ B_N that is a primary minimizer (maximizer)} tends to 0; reason: definitions of convergence in probability and of 'with high probability'
--   - encoding: min, max, Euclidean norms, Gaussian law of (G, g, h) → minMax / maxMin (real ⨅/⨆ over subtypes, attained), eNorm, gaussTriple; reason: as in Theorem 3.1
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 13, Corollary 3.2

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_MinMax

open MeasureTheory ProbabilityTheory Filter Topology

namespace IteratedLP.Gaussian

/-- Corollary 3.2 (Localization of optimizers, p. 13). A sequence of problems as in Theorem 3.1,
indexed by `N`: dimensions `n N`, `m N`, nonempty compact `C N`, `D N`, payoffs `ψ N` continuous
on `C N × D N`, and nonempty deterministic compact `B N ⊆ C N`.
(i) If `Φ_N → v` in probability and `P(ϕ_{B_N} ≥ v + δ) → 1` for some `δ > 0`, then with
probability tending to one no primary minimizer belongs to `B_N`.
(ii) For the max–min problems `max_{w∈C_N} min_{u∈D_N} {u⊤Gw + ψ(w,u)}`, if `Φ_N → v` in
probability and `P(ϕ_{B_N} ≤ v - δ) → 1` for some `δ > 0`, with
`ϕ_{B_N} = max_{w∈B_N} min_{u∈D_N} {‖w‖g⊤u + ‖u‖h⊤w + ψ(w,u)}`, then with probability tending to
one no primary maximizer belongs to `B_N`. -/
theorem corollary_3_2 (n m : ℕ → ℕ) (C B : (N : ℕ) → Set (Fin (n N) → ℝ))
    (D : (N : ℕ) → Set (Fin (m N) → ℝ))
    (ψ : (N : ℕ) → (Fin (n N) → ℝ) → (Fin (m N) → ℝ) → ℝ)
    (hC : ∀ N, IsCompact (C N) ∧ (C N).Nonempty) (hD : ∀ N, IsCompact (D N) ∧ (D N).Nonempty)
    (hψ : ∀ N, ContinuousOn (Function.uncurry (ψ N)) (C N ×ˢ D N))
    (hB : ∀ N, B N ⊆ C N ∧ IsCompact (B N) ∧ (B N).Nonempty) (v δ : ℝ) (hδ : 0 < δ) :
    ((∀ ε : ℝ, 0 < ε → Tendsto (fun N => gaussTriple (m N) (n N)
        {ω | ε < |minMax (C N) (D N) (primaryPayoff (ψ N) ω.1) - v|}) atTop (𝓝 0)) →
      Tendsto (fun N => gaussTriple (m N) (n N)
        {ω | v + δ ≤ minMax (B N) (D N) (auxPayoff (ψ N) ω.2.1 ω.2.2)}) atTop (𝓝 1) →
      Tendsto (fun N => gaussTriple (m N) (n N)
        {ω | ∃ w ∈ B N, IsMinMaxMinimizer (C N) (D N) (primaryPayoff (ψ N) ω.1) w})
        atTop (𝓝 0)) ∧
    ((∀ ε : ℝ, 0 < ε → Tendsto (fun N => gaussTriple (m N) (n N)
        {ω | ε < |maxMin (C N) (D N) (primaryPayoff (ψ N) ω.1) - v|}) atTop (𝓝 0)) →
      Tendsto (fun N => gaussTriple (m N) (n N)
        {ω | maxMin (B N) (D N) (auxPayoff (ψ N) ω.2.1 ω.2.2) ≤ v - δ}) atTop (𝓝 1) →
      Tendsto (fun N => gaussTriple (m N) (n N)
        {ω | ∃ w ∈ B N, IsMaxMinMaximizer (C N) (D N) (primaryPayoff (ψ N) ω.1) w})
        atTop (𝓝 0)) := by sorry

end IteratedLP.Gaussian
