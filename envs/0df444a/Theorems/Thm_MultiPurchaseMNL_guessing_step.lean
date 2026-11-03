-- Prove2me | Theorems.Thm_MultiPurchaseMNL_guessing_step
-- name    : MultiPurchaseMNL.guessing_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:56.174196+00:00
-- url     : https://prove2.me/theorems/7f1f014e-98d6-4c0e-93c0-65fc6d755029
-- title:
--   §4.1, p.17 — the guessing step: $S^*\subseteq H^*\cup L$, $k^*\le K$, $W/(1+\delta)\le w(L^*)\le W$, $S^*\in\mathcal F$
-- statement:
--   Let $S^*$ be an assortment and $H^*\subseteq S^*$ a set of its largest-weight products: every product of $S^*\setminus H^*$ weighs at most every product of $H^*$. Let $L$ be the light set of $H^*$, $L^*=S^*\cap L$, and suppose $L^*\neq\emptyset$. Let $\bar w=\max\{w_i:i\in L^*\}$, $\delta=\epsilon/(6m_{\max})$ with $\epsilon\in(0,1]$, and let $k^*$ be the smallest non-negative integer with $\bar w(1+\delta)^{k^*}\ge w(L^*)$. Put $W=\bar w(1+\delta)^{k^*}$. Then:
--
--   1. $S^*\subseteq H^*\cup L$, so discarding the products outside $H^*\cup L$ loses nothing;
--   2. $k^*\le K$ for every $K$ with $\bar w(1+\delta)^K\ge n\,\bar w$, so $k^*$ lies in the range the algorithm enumerates;
--   3. $\dfrac{W}{1+\delta}\le w(L^*)\le W$;
--   4. $S^*\in\mathcal F$.
--
--   These are the facts of Step 1 that make the right guess available to Step 2.
--
--   Differences from the source:
--
--   - generalization: S* an optimal assortment with |S*| > N and H* its N largest-weight products → any assortment S, any H ⊆ S whose products weigh at least every product of S \ H, with S ∩ L ≠ ∅; reason: the four facts use only these properties; the paper's S*, H* satisfy them
--   - reading: given w(L*) ∈ [w̄, n w̄], k* = O((m_max/ϵ)·log n), so k* can be enumerated → k* ≤ K for every K with w̄(1+δ)^K ≥ n·w̄; reason: this is the enumeration range the algorithm uses; the O(·) count belongs to the running-time item
--   - encoding: w̄ = max{wᵢ : i ∈ L*}; k* the smallest non-negative integer with w̄(1+δ)^k ≥ w(L*) → w̄ and k given by their defining properties as hypotheses; reason: the same numbers
--   - encoding: L = {i ∈ [n] \ H* : wᵢ ≤ min_{j∈H*} wⱼ}; F = {S ⊆ L ∪ H* : w(S ∩ L) ∈ [W/(1+δ)², (1+δ)W], S ⊇ H*} → light I H := {i ∉ H : ∀ j ∈ H, wᵢ ≤ wⱼ}; InF I H δ W S; reason: identical for nonempty H, the only case used (|H| ≥ 6m²_max/ε > 0)
--   - generalization: rᵢ > 0 (p.12) → rᵢ ≥ 0 (Standing.r_nonneg); reason: every instance with positive revenues satisfies it
--   - encoding: M supported on {0, 1, …, m_max} (§4, p.16), π(i,S) = Σ_{m∈[n]} Pr[M = m]·πₘ(i,S); m_max = O(1) presupposes m_max ≥ 1 → p : Fin (m_max+1) → ℝ with p ≥ 0, Σ p = 1; π(i,S) = Σ_{m=0}^{m_max} pₘ·πₘ(i,S) with π₀ = 0; Standing contains 1 ≤ m_max; reason: same distributions of M; the m = 0 term vanishes, and at m_max = 0 every revenue is 0 (p.12: one may assume Pr[M > 0] = 1)
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), §4.1, p.17, "Guessing heavy products" and "Guessing the total weight of light products"

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model
import Definitions.Def_MultiPurchaseMNL_ValueFunction

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), §4.1, p.17, "Step 1: Guessing".
Let `H*` (`H` below) consist of largest-weight products of an assortment `S*` (`S` below): every
product of `S* \ H*` weighs at most every product of `H*`. Let `L` be the light set,
`L* = S* ∩ L`, `w̄ = max{wᵢ : i ∈ L*}`, `δ = ϵ/(6m_max)`, and `k*` the smallest non-negative
integer with `w̄ · (1+δ)^{k*} ≥ w(L*)`. Then, with `W = w̄ · (1+δ)^{k*}`:
1. `S* ⊆ H* ∪ L` (no product of `S*` is discarded);
2. `k* ≤ K` for every `K` with `w̄ · (1+δ)^K ≥ n · w̄` (so `k*` lies in the range the algorithm
   enumerates; the paper: "Given that `w(L∗) ∈ [w̄, n w̄]`, it is easy to verify that
   `k∗ = O((m_max/ϵ) · log n)`");
3. `W/(1+δ) ≤ w(L*) ≤ W` ("clearly, `W/(1+δ) ≤ w(L∗) ≤ W`, by the choice of `k∗`");
4. `S* ∈ F`.

**Formalization Note.** `S*` is any assortment, not only an optimal one, and `H*` any such heavy
subset, of any size (the paper takes `|H*| = N` with `|S*| > N`); `L* ≠ ∅` is the existence of
`w̄`. `k*` is given by its two defining properties. Item 2 is the paper's bound on `k*` in the form the
program's loop uses. -/
theorem guessing_step {n mmax : ℕ} (I : Instance n mmax) (hI : I.Standing) (ε δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ = ε / (6 * mmax)) (S H : Finset (Fin n)) (hHS : H ⊆ S)
    (hheavy : ∀ a ∈ H, ∀ b ∈ S \ H, I.w b ≤ I.w a) (wbar : ℝ)
    (hwbar : ∃ b ∈ S ∩ light I H, I.w b = wbar) (hwbar_max : ∀ b ∈ S ∩ light I H, I.w b ≤ wbar)
    (k : ℕ) (hk : wsum I (S ∩ light I H) ≤ wbar * (1 + δ) ^ k)
    (hkmin : ∀ k' < k, wbar * (1 + δ) ^ k' < wsum I (S ∩ light I H)) :
    S ⊆ H ∪ light I H ∧
      (∀ K : ℕ, (n : ℝ) * wbar ≤ wbar * (1 + δ) ^ K → k ≤ K) ∧
      (wbar * (1 + δ) ^ k / (1 + δ) ≤ wsum I (S ∩ light I H) ∧
        wsum I (S ∩ light I H) ≤ wbar * (1 + δ) ^ k) ∧
      InF I H δ (wbar * (1 + δ) ^ k) S := by sorry

end MultiPurchaseMNL
