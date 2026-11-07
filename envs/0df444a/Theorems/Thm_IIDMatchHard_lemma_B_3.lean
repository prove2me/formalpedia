-- Prove2me | Theorems.Thm_IIDMatchHard_lemma_B_3
-- name    : IIDMatchHard.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:17.192691+00:00
-- url     : https://prove2.me/theorems/c0cde816-b931-409e-834c-e926d45eb466
-- title:
--   Lemma B.3 — net gains of an edge
-- statement:
--   Let $G$ be a finite simple graph, $\lambda>0$, $t\in[0,1]$ and let $e=(u,v)$ be an edge of $G$, in the adjusted Poisson model of $I(G,\lambda)$.
--
--   1. For every deterministic greedy policy $\pi$ of the adjusted model, with signs $\theta_t$,
--   $$P_e(t)\sum_{s\in\{+,-\}}\sum_{d=1}^2h_d(t)\,Q^s_{e,d}(t)\ \le\ \mathbb E[\Gamma_e(t)]+h_1(t)\,\mathbb P\big(X_u(t)=X_v(t)=1,\ \theta_t(u)\ne\theta_t(v)\big).$$
--   2. For the policy $\pi_\sigma$ of a cut $\sigma$ of $G$,
--   $$\sum_{s\in\{+,-\}}\sum_{d=1}^2h_d(t)\,Q^s_{e,d}(t)=\mathbb E[\Gamma_e(t)]+h_1(t)\,t^2e^{-2t}\,\mathbf 1[\sigma(u)\ne\sigma(v)].$$
--   3. $$\int_0^1\mathbb E[\Gamma_e(t)]\,dt=\frac1e+\frac9{e^2},\qquad\int_0^1h_1(t)\,t^2e^{-2t}\,dt=\frac2e-\frac5{e^2}.$$
--
--   The net gain of an edge exceeds the baseline $\mathbb E[\Gamma_e(t)]$ only when the free vertices at its endpoints have different signs. For $\pi_\sigma$ this happens exactly on the edges $\sigma$ cuts, which links Poisson values to cuts.
--
--   Differences from the source:
--   - generalization: π_σ with ties broken by a fixed order of V → π_σ for every linear order o of V; reason: the paper order is one such order
--   - encoding: parts (a) and (b) for t ∈ [0, 1] → universally quantified over t ∈ [0, 1] in one conjunction with (c); reason: same claims
--   - encoding: E[Γ_e(t)] → a lower Lebesgue integral of the nonnegative bounded Γ_e(t), converted to ℝ; reason: same value
--   - encoding: the adjusted Poisson model (a Poisson process of rate R with i.i.d. types) → the law cutLaw on (ℝ × Y)^ℕ, i.i.d. exponential gaps with independent types, K(t) the Set.ncard of {k : τ_{k+1} ≤ t}, arrivals 0-based; reason: the same process; K(t) differs only on a null event (infinitely many points, or a negative gap)
--   - encoding: a deterministic policy → a function of the earlier types, the matched set and the current type; a proposal that is not a free neighbor is a rejection; reason: the matched set is a function of the earlier types for a deterministic policy; same class of policies
--   - encoding: P_e(t) and Q^s_{e,d}(t) → P_e computed for the sign +; Q the probability of (I) and (II) divided by P_e; reason: blocked arrivals do not depend on the sign; P_e(t) > 0, so the ratio is the conditional probability
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Lemma B.3, p.18 (PDF p.19); proof pp.19–20

import Definitions.Def_IIDMatchHard_Adjusted

set_option autoImplicit false

namespace IIDMatchHard

/-- **Lemma B.3.** Let `t ∈ [0, 1]` and let `e = (u, v)` be an edge of `G`.
(a) For every deterministic greedy policy `π` of the adjusted model,
`P_e(t) ∑_{s ∈ {+,−}} ∑_{d=1}^2 h_d(t) Q^s_{e,d}(t) ≤ E[Γ_e(t)] + h₁(t) P(X_u(t) = X_v(t) = 1, θ_t(u) ≠ θ_t(v))`.
(b) For the policy `π_σ` of a cut `σ` of `G`,
`∑_{s ∈ {+,−}} ∑_{d=1}^2 h_d(t) Q^s_{e,d}(t) = E[Γ_e(t)] + h₁(t) t² e^{−2t} 1[σ(u) ≠ σ(v)]`.
(c) `∫₀¹ E[Γ_e(t)] dt = 1/e + 9/e²` and `∫₀¹ h₁(t) t² e^{−2t} dt = 2/e − 5/e²`.
Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Lemma B.3, p.18 (PDF p.19); proof pp.19–20.

**Formalization Note.** Parts (a) and (b) are stated for every `t ∈ [0, 1]`. In (a), `θ_t` is the
sign function of `π` (App. B.5, p.18). In (b), `π_σ` breaks ties by any fixed order `o` of `V`
and is run in the adjusted model. -/
theorem lemma_B_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (lam : ℝ)
    (hlam : 0 < lam) (u v : V) (huv : G.Adj u v) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ π : Policy (V × Bool) (IType G), IsGreedy (adjNbr G) π →
      probUnblocked G lam ⟨s(u, v), G.mem_edgeSet.2 huv⟩ t *
          ∑ s : Bool, ∑ d ∈ Finset.Icc 1 2,
            hNet d t * probMatch G lam π ⟨s(u, v), G.mem_edgeSet.2 huv⟩ s d t ≤
        expGamma G lam t u v + hNet 1 t *
          (cutLaw G lam {ω | vtxCount G ω t u = 1 ∧ vtxCount G ω t v = 1 ∧
            theta G π ω t u ≠ theta G π ω t v}).toReal) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ (o : LinearOrder V) (σ : V → Bool),
      ∑ s : Bool, ∑ d ∈ Finset.Icc 1 2,
          hNet d t * probMatch G lam (cutPolicy G o σ) ⟨s(u, v), G.mem_edgeSet.2 huv⟩ s d t =
        expGamma G lam t u v +
          hNet 1 t * (t ^ 2 * Real.exp (-2 * t)) * (if σ u ≠ σ v then 1 else 0)) ∧
    (∫ t in (0 : ℝ)..1, expGamma G lam t u v) = 1 / Real.exp 1 + 9 / Real.exp 1 ^ 2 ∧
    (∫ t in (0 : ℝ)..1, hNet 1 t * (t ^ 2 * Real.exp (-2 * t))) =
      2 / Real.exp 1 - 5 / Real.exp 1 ^ 2 := by sorry

end IIDMatchHard
