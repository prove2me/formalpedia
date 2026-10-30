-- Prove2me | Theorems.Thm_MultimodalPricing_Regret_lemma_2
-- name    : MultimodalPricing.Regret.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T08:02:58.003278+00:00
-- url     : https://prove2.me/theorems/1726a0a5-217a-4cf2-8428-bd22a16a07a4
-- title:
--   Lemma 2 — one call of BiasedLinearBandit
-- statement:
--   Let $f\in\Sigma^k([a,b];C)$, $0\le a\le b\le p_{\max}$, $t\ge1$, $\Delta\ge C(b-a)^k$ and $0<\delta<1$. Let $t$ adaptive bounded-demand observations in $[a,b]$ obey the sequential mean model. If a price $\widehat p$, measurable at the end of that history, is any output of Algorithm 2, then the outer probability that the following inequality fails is at most $\delta$:
--   $$\max_{p\in[a,b]}pf(p)-\widehat p f(\widehat p)\le2p_{\max}\min\{1,\gamma\sqrt{\phi(\widehat p)^\top\Lambda^{-1}\phi(\widehat p)}+\Delta\},$$
--   where $\gamma=C\sqrt k+\Delta\sqrt t+\sqrt{2k\log(4kt/\delta)}+2$, and $\Lambda,\phi$ and the ridge estimate are computed from that history. No interval-length restriction or accurate-estimate hypothesis is added.
--
--   Differences from the source:
--   - generalization: economic price interval → finite nonnegative real endpoints with 0 ≤ a ≤ b, including a singleton; reason: makes the economic nonnegative-price convention explicit, as required by the revenue comparison on p. 32; singleton intervals are additionally admitted
--   - encoding: (k−1) derivatives on the closed price interval → a tower of successive HasDerivWithinAt derivatives, with order zero equal to f on the interval; reason: uses one-sided endpoint derivatives, imposes no condition outside the interval, and at k=1 requires only the printed bounded Lipschitz condition
--   - reading: the price-conditioned mean on p. 9 and full-history centered noise on p. 32 → a measurable probability kernel on finite observation histories and current price, supported in [0,1] with mean f(p), realized by conditional-law integral identities; reason: makes the operational sequential model explicit without independence or a concentration assumption
--   - generalization: randomized decisions based on observed history → decisions measurable in any predecision filtration for which the same history-and-price kernel is the conditional demand law; reason: the observed-history filtration with private randomization is a special case; no future demand may invalidate the conditional law
--   - encoding: rounds 1 through t and vector coordinates 0 through k−1 → rounds in Finset.range t, ordered lists retaining repetitions, and vectors Fin k → ℝ; reason: reindexing changes no observation or coefficient
--   - reading: centered features in Algorithm 2, conflicting with uncentered features in the explanatory p. 13 prose → features (1,p−a,…,(p−a)^(k−1)) as explicitly printed in Algorithm 2; reason: the algorithm and Lemma 1 agree; the inconsistent prose identity is recorded as finding I5
--   - encoding: maximum expected revenue on a closed interval → sSup of the image of p ↦ p f(p); reason: Smooth implies continuity on a nonempty compact interval, so this supremum is finite and attained
--   - encoding: with probability at least 1−δ or 1−O(1/T) → outer measure of the strict bad event at most δ or B/T; reason: agrees on measurable events and avoids assuming measurability of an uncountable supremum
--   - encoding: |D|=t in a numerical formula containing log(t) → t≥1 and a genuine adaptive history of that length; reason: only the domain of the displayed logarithm is excluded; full trajectories elsewhere still begin empty
--   - generalization: p_max is the containing market endpoint → any nonnegative upper bound p_max with b≤p_max; reason: each source interval and its market upper endpoint satisfy this condition
-- source:
--   Wang, Chen, Simchi-Levi, Multi-Modal Dynamic Pricing, https://doi.org/10.1287/mnsc.2020.3819, supplied artifact (published metadata; SSRN 3489355 footer), Lemma 2, printed/PDF p. 14; Algorithm 2, p. 11; proof setup, p. 32

import Definitions.Def_MultimodalPricing_Regret_LocalBandit

open MeasureTheory MultimodalPricing.Regret

namespace MultimodalPricing.Regret

theorem lemma_2
    (k t : ℕ) (ht : 1 ≤ t) (C a b pmax Δ δ : ℝ) (f : ℝ → ℝ)
    (hf : Smooth k C a b f) (ha : 0 ≤ a) (hpmax : b ≤ pmax)
    (hΔ : C * (b - a) ^ k ≤ Δ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (O : Observation Ω) (hO : IsObservation μ t a b f O)
    (pout : Ω → ℝ) (hpout : Measurable[O.info t] pout)
    (hcall : ∀ᵐ ω ∂μ,
      LocalChoice k a b C Δ δ (history O.price O.demand t ω) (pout ω)) :
    μ {ω | 2 * pmax * min 1
        (radius k t C Δ δ * uncertainty k a (history O.price O.demand t ω) (pout ω) + Δ)
      < bestReward a b f - reward f (pout ω)} ≤ ENNReal.ofReal δ := by sorry

end MultimodalPricing.Regret
