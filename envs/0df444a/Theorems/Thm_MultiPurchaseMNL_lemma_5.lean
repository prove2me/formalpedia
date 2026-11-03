-- Prove2me | Theorems.Thm_MultiPurchaseMNL_lemma_5
-- name    : MultiPurchaseMNL.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:43.664202+00:00
-- url     : https://prove2.me/theorems/4b5c2610-acd6-4281-9d4a-baecbaf1845b
-- title:
--   Lemma 5 — the proxies $\mathbb E[V(i,M,H^*)]$ are within $1-2\epsilon$ of $\pi(i,S)$ on $\mathcal F$
-- statement:
--   Fix $\epsilon\in(0,1]$, $\delta=\epsilon/(6m_{\max})$, a heavy set $H^*$ with $|H^*|\ge6m_{\max}^2/\epsilon$, its light set, a guess $W$, the family $\mathcal F$ and the value function $V$ of (4). For any assortment $S\in\mathcal F$ and any product $i\in S$,
--   $$
--   (1-2\epsilon)\,\pi(i,S)\ \le\ \mathbb E\big[V(i,M,H^*)\big]\ \le\ \pi(i,S),
--   $$
--   where the expectation is over $M$ only: $\mathbb E[V(i,M,H^*)]=\sum_m\Pr[M=m]\,V(i,m,H^*)$.
--
--   The lemma replaces the assortment-dependent choice probabilities by assortment-independent proxies $\tilde\pi_i$, turning the assortment problem into the knapsack problem (5).
--
--   Differences from the source:
--
--   - generalization: |H*| = N = 6m²_max/ϵ with 1/ϵ an integer (§4.1, p.17), δ = ϵ/(6m_max) → any H with 6m²_max/ε ≤ |H|, any ε ∈ (0,1], δ = ε/(6m_max); reason: the proofs use only m_max/|H*| ≤ δ (App. C.2, p.41) and δ ≤ 1/6; the paper's setting is the case |H| = 6m²_max/ε, 1/ε ∈ ℕ
--   - encoding: E[V(i,M,H*)] over the randomness in M → proxy I δ W H i = Σ_{m=0}^{m_max} pₘ·V(i,m,H); reason: the definition of the expectation over the support of M
--   - encoding: L = {i ∈ [n] \ H* : wᵢ ≤ min_{j∈H*} wⱼ}; F = {S ⊆ L ∪ H* : w(S ∩ L) ∈ [W/(1+δ)², (1+δ)W], S ⊇ H*} → light I H := {i ∉ H : ∀ j ∈ H, wᵢ ≤ wⱼ}; InF I H δ W S; reason: identical for nonempty H, the only case used (|H| ≥ 6m²_max/ε > 0)
--   - generalization: rᵢ > 0 (p.12) → rᵢ ≥ 0 (Standing.r_nonneg); reason: every instance with positive revenues satisfies it
--   - encoding: M supported on {0, 1, …, m_max} (§4, p.16), π(i,S) = Σ_{m∈[n]} Pr[M = m]·πₘ(i,S); m_max = O(1) presupposes m_max ≥ 1 → p : Fin (m_max+1) → ℝ with p ≥ 0, Σ p = 1; π(i,S) = Σ_{m=0}^{m_max} pₘ·πₘ(i,S) with π₀ = 0; Standing contains 1 ≤ m_max; reason: same distributions of M; the m = 0 term vanishes, and at m_max = 0 every revenue is 0 (p.12: one may assume Pr[M > 0] = 1)
--   - encoding: products 1..n and the no-purchase option 0; Uᵢ = vᵢ + eᵢ with e₀,…,eₙ i.i.d. standard Gumbel (0,1), v₀ = 0; wᵢ = e^{vᵢ} → products Fin n, option 0 = none : Option (Fin n); shocks under Measure.pi of μ with IsExtremeValue μ; vᵢ = log wᵢ with wᵢ > 0, so w₀ = 1; reason: same model: wᵢ = e^{vᵢ} > 0 is exactly vᵢ = log wᵢ, and IsExtremeValue is the standard Gumbel cdf
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), Lemma 5, p.18 (proof §4.4, pp.20–21)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model
import Definitions.Def_MultiPurchaseMNL_ValueFunction

open MeasureTheory ProbabilityTheory

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), **Lemma 5**, p.18: for any assortment
`S ∈ F` and product `i ∈ S`, `(1 − 2ϵ) · π(i, S) ≤ E[V(i, M, H*)] ≤ π(i, S)`, where the expectation
is taken over the randomness in `M`.

The setting is that of §4.1–§4.2, pp.17–18: `0 < ϵ ≤ 1`, `δ = ϵ/(6m_max)`, a heavy set `H*`
(`H` below) with `|H*| ≥ 6m²_max/ϵ`, its light set, a guess `W`, `F` and the value function (4).
`E[V(i, M, H*)] = Σₘ Pr[M = m] · V(i, m, H*)` is `proxy`.

**Formalization Note.** The paper has `|H*| = 6m²_max/ϵ` with `1/ϵ` an integer; here
`|H*| ≥ 6m²_max/ϵ` and `ϵ ∈ (0, 1]`. -/
theorem lemma_5 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : McFadden1974.RandomUtility.IsExtremeValue μ) {n mmax : ℕ} (I : Instance n mmax)
    (hI : I.Standing) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ = ε / (6 * mmax))
    (H : Finset (Fin n)) (hH : 6 * (mmax : ℝ) ^ 2 / ε ≤ H.card) (W : ℝ) (S : Finset (Fin n))
    (hS : InF I H δ W S) (i : Fin n) (hi : i ∈ S) :
    (1 - 2 * ε) * choiceProb μ I i S ≤ proxy I δ W H i ∧
      proxy I δ W H i ≤ choiceProb μ I i S := by sorry

end MultiPurchaseMNL
