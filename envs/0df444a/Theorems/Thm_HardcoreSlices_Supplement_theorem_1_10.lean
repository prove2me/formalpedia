-- Prove2me | Theorems.Thm_HardcoreSlices_Supplement_theorem_1_10
-- name    : HardcoreSlices.Supplement.theorem_1_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:28:51.90978+00:00
-- url     : https://prove2.me/theorems/fecce81a-b951-4c5b-b41e-453104134e99
-- title:
--   Theorem 1.10 — the independent set slice of a random $\Delta$-regular graph is a top-link expander below $(1-\gamma')\alpha^*(\Delta)$
-- statement:
--   Let $\alpha^*(\Delta)=\frac{\log\Delta}{2\Delta}$ (natural logarithm). There is a sequence $\gamma'(\Delta)\to0$ such that for every sufficiently large $\Delta$ we have $0<\gamma'(\Delta)<1$ and there are constants $K,r$ (depending on $\Delta$) with the following property. With probability tending to $1$ as $n\to\infty$ (along $n\Delta$ even), a uniformly random simple $\Delta$-regular graph $G$ on $n$ vertices satisfies, for every integer $k$ with
--   $$1\le k\le(1-\gamma'(\Delta))\,\alpha^*(\Delta)\,n,$$
--
--   1. the set $\mathcal I_k(G)$ of independent sets of size $k$ is nonempty;
--   2. the independent set slice $(X,\mu^{(k)})$ is a connected $\frac1{2k}$-top-link spectral expander: the walk on the link of every face of size $k-2$ has second eigenvalue at most $\frac1{2k}$, and the link of every face of size at most $k-2$ (including $\emptyset$) has a connected underlying graph;
--   3. the down-up walk from any facet is within total variation $\varepsilon$ of $\mu^{(k)}$ at every time $t\ge K(n+1+\log(1/\varepsilon))^r$, for all $\varepsilon\in(0,1)$.
--
--   This is the non-bipartite counterpart of Theorem 1.8: it shows that the down-up walk on the uniform distribution over independent sets of a fixed size mixes in polynomial time on random regular graphs well beyond the worst-case critical occupancy $\alpha_c(\Delta)\sim\frac{e}{1+e}\frac1\Delta$.
--
--   **Formalization Note** "With high probability" is the published `PottsRapidMixing.WithHighProb`; $\gamma'$, $\Delta_0$, $K$, $r$ are fixed before $n$ and $G$, and $k$ is quantified inside the event. Top-link expansion is the published `HDXConc.IsTopLinkExpander`; polynomial-time mixing is the mission's published `MixesInPoly`.
--
--   Differences from the source:
--   - reading: "some fixed constant γ′ > 0" (p.4) and "γ′ = o∆(1)" (p.37) → ∃ γ′ : ℕ → ℝ with γ′(∆) → 0 and 0 < γ′(∆) < 1 for ∆ ≥ ∆₀; reason: the proof fixes γ′ = o∆(1); this reading implies the constant one, since γ′(∆) eventually lies below any fixed constant
--   - reading: the sentence states no condition on ∆ → every ∆ ≥ ∆₀ for some ∆₀; reason: γ′ = o∆(1) and α∗(∆) are asymptotic in ∆ and the proof takes ∆ large (pp.3, 37), as in Theorem 1.8
--   - reading: mixes in polynomial-time → K (n + 1 + log 1/ε)^r with K, r chosen for each ∆, before n and G; reason: ∆ is large but fixed (p.2), and Theorem 1.2 gives this form, as in Theorem 1.8
--   - reading: k ≤ α|V| → also 1 ≤ k; reason: at k = 0 the bound 1/(2·0) and the walk have no meaning
--   - generalization: the expander and mixing claims for the slice → also the conclusion that I_k(G) is nonempty; reason: it keeps µ^(k) a real distribution, the paper's definition of µ^(k) presupposes it, and the remaining clauses are the source's claim unchanged
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Theorem 1.10, p.4 (proof in Appendix A, pp.36–37)

import Mathlib
import Definitions.Def_HardcoreSlices_IsThreshold
import Definitions.Def_HardcoreSlices_downUp
import Definitions.Def_HardcoreSlices_Supplement_indepSlice
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_PottsRapidMixing_Ensemble

open Classical Filter Topology

namespace HardcoreSlices.Supplement

/-- **Theorem 1.10.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite
Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.4 (proof in Appendix A,
pp.36–37): "Let `G = (V, E)` be a random `∆`-regular graph. Then with high probability over the randomness of `G`, the
independent set slice `(X, µ(k))` for `k ≤ α|V|` with `α = (1 − γ′)α∗(∆)` fixed above is a connected `1/(2k)`-top-link
spectral expander, and as a result, the down-up walk mixes in polynomial-time."

**Formalization Note.** The random graph is the uniform simple `∆`-regular graph on `Fin n`, and "with high
probability" is the published `PottsRapidMixing.WithHighProb` (probability tending to `1` along `n∆` even).
`γ′` is the proof's `γ′ = o∆(1)` (p.37): a sequence in `(0, 1)` for large `∆` tending to `0`; this implies the
introduction's "some fixed constant `γ′ > 0`" (p.4). `α∗` is the published `HardcoreSlices.alphaStar`
(`log ∆/(2∆)`, p.3). `γ′`, `∆₀` and the polynomial's `K, r` (which may depend on `∆`) are chosen before `n` and
the graph; `k` is quantified inside the event, over every `1 ≤ k ≤ (1 − γ′(∆))α∗(∆)n`. `k = 0` is excluded, as
`1/(2·0)` and a `0`-dimensional walk mean nothing. "Mixes in polynomial-time" is the published
`HardcoreSlices.MixesInPoly`, the time bound `K(n + 1 + log 1/ε)^r` from every facet. The slice is also asserted
nonempty, so `µ^{(k)}` is a real distribution. -/
theorem theorem_1_10 :
    ∃ γ' : ℕ → ℝ, Tendsto γ' atTop (𝓝 0) ∧
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → 0 < γ' Δ ∧ γ' Δ < 1 ∧
      ∃ K r : ℕ, PottsRapidMixing.WithHighProb Δ (fun n G =>
        ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ (1 - γ' Δ) * alphaStar Δ * n →
          (indepFacets G k).Nonempty ∧
          HDXConc.IsTopLinkExpander (indepComplex G k) k (indepLaw G k) (1 / (2 * (k : ℝ))) ∧
          MixesInPoly (indepComplex G k) k (indepLaw G k) K r n) := by sorry

end HardcoreSlices.Supplement
