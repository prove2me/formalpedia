-- Prove2me | Theorems.Thm_IIDMatchHard_lemma_3_5
-- name    : IIDMatchHard.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:04.358326+00:00
-- url     : https://prove2.me/theorems/a166d78f-2d01-48b0-89e4-1c39a93202b5
-- title:
--   Lemma 3.5 — the Poisson value of a greedy policy
-- statement:
--   Let $G$ be a finite simple graph and $\lambda>0$. For every deterministic greedy policy $\pi$ of the adjusted Poisson model of $I(G,\lambda)$,
--   $$\mathbb E[\widehat M_\pi]=\Big(2-\frac3e\Big)n+\lambda\sum_{e\in E}\ \sum_{s\in\{+,-\}}\ \sum_{d\in\{0,1,2\}}\int_0^1h_d(t)\,P_e(t)\,Q^s_{e,d}(t)\,dt.$$
--   Here $h_d$ is the net gain of a match into a pair with $d$ free vertices, $P_e(t)$ is the probability that an edge arrival of $e$ at time $t$ is not blocked, and $Q^s_{e,d}(t)$ is the conditional probability that $\pi$ matches an arrival of type $e^s$ into a pair with $d$ free vertices.
--
--   The Poisson value splits into the baseline $(2-3/e)n$ of the vertex arrivals and the net gains of the matched edge arrivals.
--
--   Differences from the source:
--   - reading: a deterministic greedy policy → a policy greedy for the adjusted neighbor sets, run in the adjusted model; reason: App. B.4 runs π in the adjusted model; App. B.5 calls π_σ "a greedy policy of the adjusted model"
--   - encoding: e in 2 − 3/e; ∫₀¹; d ∈ {0, 1, 2} → Real.exp 1; the interval integral over [0, 1]; Finset.range 3; reason: Lean convention; same quantities
--   - encoding: the adjusted Poisson model (a Poisson process of rate R with i.i.d. types) → the law cutLaw on (ℝ × Y)^ℕ, i.i.d. exponential gaps with independent types, K(t) the Set.ncard of {k : τ_{k+1} ≤ t}, arrivals 0-based; reason: the same process; K(t) differs only on a null event (infinitely many points, or a negative gap)
--   - encoding: E[M̂_π] → a lower Lebesgue integral of the count converted to ℝ; reason: the count is nonnegative and at most 2n; same value
--   - encoding: a deterministic policy → a function of the earlier types, the matched set and the current type; a proposal that is not a free neighbor is a rejection; reason: the matched set is a function of the earlier types for a deterministic policy; same class of policies
--   - encoding: P_e(t) and Q^s_{e,d}(t) → P_e computed for the sign +; Q the probability of (I) and (II) divided by P_e; reason: blocked arrivals do not depend on the sign; P_e(t) > 0, so the ratio is the conditional probability
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Lemma 3.5, p.8 (PDF p.9); proof in App. B.4, pp.17–18

import Definitions.Def_IIDMatchHard_Adjusted

set_option autoImplicit false

namespace IIDMatchHard

open Classical in
/-- **Lemma 3.5 (Poisson value).** For any deterministic greedy policy `π`,
`E[M̂_π] = (2 − 3/e)n + λ ∑_{e ∈ E} ∑_{s ∈ {+,−}} ∑_{d ∈ {0,1,2}} ∫₀¹ h_d(t) P_e(t) Q^s_{e,d}(t) dt`.
Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Lemma 3.5, p.8 (PDF p.9); proof in App. B.4, pp.17–18.

**Formalization Note.** `π` is greedy for the adjusted neighbor sets and is run in the adjusted
model (App. B.4 fixes "π processes y_1, …, y_ℓ in the adjusted model"; App. B.5: π_σ "is a greedy
policy of the adjusted model"). `e` in `2 − 3/e` is `exp 1`; `d ∈ {0, 1, 2}` is
`Finset.range 3`; `∫₀¹` is the interval integral. -/
theorem lemma_3_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (lam : ℝ)
    (hlam : 0 < lam) (π : Policy (V × Bool) (IType G)) (hπ : IsGreedy (adjNbr G) π) :
    poissonValue G lam π =
      (2 - 3 / Real.exp 1) * (Fintype.card V : ℝ) +
        lam * ∑ e : G.edgeSet, ∑ s : Bool, ∑ d ∈ Finset.range 3,
          ∫ t in (0 : ℝ)..1, hNet d t * probUnblocked G lam e t * probMatch G lam π e s d t := by sorry

end IIDMatchHard
