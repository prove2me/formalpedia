-- Prove2me | Theorems.Thm_MultiPurchaseMNL_claim_3
-- name    : MultiPurchaseMNL.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:52.1433+00:00
-- url     : https://prove2.me/theorems/219ee903-2da4-4f91-8ea1-5622444f3027
-- title:
--   Claim 3 — $V$ approximates $\pi_m$ on sub-assortments of $S\in\mathcal F$
-- statement:
--   Fix $\epsilon\in(0,1]$, $\delta=\epsilon/(6m_{\max})$, a heavy set $H^*$ with $|H^*|\ge6m_{\max}^2/\epsilon$, its light set, a guess $W$, the family $\mathcal F$ and the value function $V$ of (4). Let $S\in\mathcal F$, $i\in S$, and let $Q\subseteq S$ with $i\in Q$ and $|S\setminus Q|\le m_{\max}-m$ for some $m\in\{1,\dots,m_{\max}\}$. Then
--   $$
--   (1-\delta)^{6m}\,\pi_m(i,Q)\ \le\ V(i,m,H^*\cap Q)\ \le\ \pi_m(i,Q).
--   $$
--   This is the generalized claim from which Lemma 5 follows by taking $Q=S$.
--
--   Differences from the source:
--
--   - generalization: |H*| = N = 6m²_max/ϵ with 1/ϵ an integer (§4.1, p.17), δ = ϵ/(6m_max) → any H with 6m²_max/ε ≤ |H|, any ε ∈ (0,1], δ = ε/(6m_max); reason: the proofs use only m_max/|H*| ≤ δ (App. C.2, p.41) and δ ≤ 1/6; the paper's setting is the case |H| = 6m²_max/ε, 1/ε ∈ ℕ
--   - encoding: m ∈ [m_max], |S \ Q| ≤ m_max − m → 1 ≤ m and |S \ Q| + m ≤ m_max; reason: the same condition without natural-number subtraction
--   - encoding: L = {i ∈ [n] \ H* : wᵢ ≤ min_{j∈H*} wⱼ}; F = {S ⊆ L ∪ H* : w(S ∩ L) ∈ [W/(1+δ)², (1+δ)W], S ⊇ H*} → light I H := {i ∉ H : ∀ j ∈ H, wᵢ ≤ wⱼ}; InF I H δ W S; reason: identical for nonempty H, the only case used (|H| ≥ 6m²_max/ε > 0)
--   - generalization: rᵢ > 0 (p.12) → rᵢ ≥ 0 (Standing.r_nonneg); reason: every instance with positive revenues satisfies it
--   - encoding: M supported on {0, 1, …, m_max} (§4, p.16), π(i,S) = Σ_{m∈[n]} Pr[M = m]·πₘ(i,S); m_max = O(1) presupposes m_max ≥ 1 → p : Fin (m_max+1) → ℝ with p ≥ 0, Σ p = 1; π(i,S) = Σ_{m=0}^{m_max} pₘ·πₘ(i,S) with π₀ = 0; Standing contains 1 ≤ m_max; reason: same distributions of M; the m = 0 term vanishes, and at m_max = 0 every revenue is 0 (p.12: one may assume Pr[M > 0] = 1)
--   - encoding: products 1..n and the no-purchase option 0; Uᵢ = vᵢ + eᵢ with e₀,…,eₙ i.i.d. standard Gumbel (0,1), v₀ = 0; wᵢ = e^{vᵢ} → products Fin n, option 0 = none : Option (Fin n); shocks under Measure.pi of μ with IsExtremeValue μ; vᵢ = log wᵢ with wᵢ > 0, so w₀ = 1; reason: same model: wᵢ = e^{vᵢ} > 0 is exactly vᵢ = log wᵢ, and IsExtremeValue is the standard Gumbel cdf
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), Claim 3, p.20 (proofs §4.4, pp.20–21, and App. C.3, pp.41–42)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model
import Definitions.Def_MultiPurchaseMNL_ValueFunction

open MeasureTheory ProbabilityTheory

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), **Claim 3**, p.20: for an assortment
`S ∈ F` and a product `i ∈ S` ("consider some assortment `S ∈ F` and a product `i ∈ S`"), let
`Q ⊆ S` be a subset of products with `i ∈ Q` (so `i ∈ S`), and suppose that `|S \ Q| ≤ m_max − m` for some
`m ∈ [m_max]`. Then `(1 − δ)^{6m} · πₘ(i, Q) ≤ V(i, m, H* ∩ Q) ≤ πₘ(i, Q)`.

The setting is that of §4.1–§4.2, pp.17–18: `0 < ϵ ≤ 1`, `δ = ϵ/(6m_max)`, a heavy set `H*`
(`H` below) with `|H*| ≥ 6m²_max/ϵ`, its light set, a guess `W`, `F` and the value function (4).

**Formalization Note.** `m ∈ [m_max]` and `|S \ Q| ≤ m_max − m` are written `1 ≤ m` and
`|S \ Q| + m ≤ m_max`. The paper has `|H*| = 6m²_max/ϵ` with `1/ϵ` an integer. -/
theorem claim_3 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : McFadden1974.RandomUtility.IsExtremeValue μ) {n mmax : ℕ} (I : Instance n mmax)
    (hI : I.Standing) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ = ε / (6 * mmax))
    (H : Finset (Fin n)) (hH : 6 * (mmax : ℝ) ^ 2 / ε ≤ H.card) (W : ℝ) (S : Finset (Fin n))
    (hS : InF I H δ W S) (i : Fin n) (Q : Finset (Fin n)) (hQ : Q ⊆ S)
    (hiQ : i ∈ Q) (m : ℕ) (hm1 : 1 ≤ m) (hm : (S \ Q).card + m ≤ mmax) :
    (1 - δ) ^ (6 * m) * piM μ I m i Q ≤ V I δ W i m (H ∩ Q) ∧
      V I δ W i m (H ∩ Q) ≤ piM μ I m i Q := by sorry

end MultiPurchaseMNL
