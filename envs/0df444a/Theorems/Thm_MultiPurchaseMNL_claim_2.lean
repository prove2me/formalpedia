-- Prove2me | Theorems.Thm_MultiPurchaseMNL_claim_2
-- name    : MultiPurchaseMNL.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:43.57118+00:00
-- url     : https://prove2.me/theorems/d39c6379-9a3a-457f-aa73-d9050b05ccd7
-- title:
--   Claim 2 — light weight survives removing at most $m_{\max}$ products
-- statement:
--   Fix $\epsilon\in(0,1]$, $\delta=\epsilon/(6m_{\max})$, a heavy set $H^*$ with $|H^*|\ge 6m_{\max}^2/\epsilon$, its light set $L$ and a guess $W$, and let $\mathcal F$ be the family of §4.2. Let $S\in\mathcal F$ and let $Q\subseteq S$ with $|S\setminus Q|\le m_{\max}$. Then
--   $$
--   w(Q\cap L)\ \ge\ \frac{W}{(1+\delta)^2}-\delta\cdot w(Q\cap H^*).
--   $$
--   The claim bounds from below the light weight left in a sub-assortment; it controls part (ii) of the value function (4) in the proof of Claim 3.
--
--   Differences from the source:
--
--   - generalization: |H*| = N = 6m²_max/ϵ with 1/ϵ an integer (§4.1, p.17), δ = ϵ/(6m_max) → any H with 6m²_max/ε ≤ |H|, any ε ∈ (0,1], δ = ε/(6m_max); reason: the proofs use only m_max/|H*| ≤ δ (App. C.2, p.41) and δ ≤ 1/6; the paper's setting is the case |H| = 6m²_max/ε, 1/ε ∈ ℕ
--   - encoding: L = {i ∈ [n] \ H* : wᵢ ≤ min_{j∈H*} wⱼ}; F = {S ⊆ L ∪ H* : w(S ∩ L) ∈ [W/(1+δ)², (1+δ)W], S ⊇ H*} → light I H := {i ∉ H : ∀ j ∈ H, wᵢ ≤ wⱼ}; InF I H δ W S; reason: identical for nonempty H, the only case used (|H| ≥ 6m²_max/ε > 0)
--   - generalization: rᵢ > 0 (p.12) → rᵢ ≥ 0 (Standing.r_nonneg); reason: every instance with positive revenues satisfies it
--   - encoding: M supported on {0, 1, …, m_max} (§4, p.16), π(i,S) = Σ_{m∈[n]} Pr[M = m]·πₘ(i,S); m_max = O(1) presupposes m_max ≥ 1 → p : Fin (m_max+1) → ℝ with p ≥ 0, Σ p = 1; π(i,S) = Σ_{m=0}^{m_max} pₘ·πₘ(i,S) with π₀ = 0; Standing contains 1 ≤ m_max; reason: same distributions of M; the m = 0 term vanishes, and at m_max = 0 every revenue is 0 (p.12: one may assume Pr[M > 0] = 1)
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), Claim 2, p.20 (proof App. C.2, pp.40–41)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model
import Definitions.Def_MultiPurchaseMNL_ValueFunction

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), **Claim 2**, p.20: let `S ∈ F` be an
assortment and let `Q ⊆ S` be a subset of products with `|S \ Q| ≤ m_max`. Then
`w(Q ∩ L) ≥ W/(1+δ)² − δ · w(Q ∩ H*)`.

The setting is that of §4.1–§4.2, pp.17–18: `0 < ϵ ≤ 1`, `δ = ϵ/(6m_max)`, a heavy set `H*`
(`H` below) with `|H*| ≥ N = 6m²_max/ϵ`, its light set `L`, a guess `W` and the family `F`.

**Formalization Note.** The paper has `|H*| = N` and `1/ϵ` an integer; here `|H*| ≥ 6m²_max/ϵ` and
`ϵ ∈ (0, 1]` (the proof uses only `m_max/|H*| ≤ δ`). -/
theorem claim_2 {n mmax : ℕ} (I : Instance n mmax) (hI : I.Standing) (ε δ : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : δ = ε / (6 * mmax)) (H : Finset (Fin n))
    (hH : 6 * (mmax : ℝ) ^ 2 / ε ≤ H.card) (W : ℝ) (S : Finset (Fin n)) (hS : InF I H δ W S)
    (Q : Finset (Fin n)) (hQ : Q ⊆ S) (hSQ : (S \ Q).card ≤ mmax) :
    W / (1 + δ) ^ 2 - δ * wsum I (Q ∩ H) ≤ wsum I (Q ∩ light I H) := by sorry

end MultiPurchaseMNL
