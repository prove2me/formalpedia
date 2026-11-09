-- Prove2me | Theorems.Thm_KTaxi_Competitive_claim_4_6
-- name    : KTaxi.Competitive.claim_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:29:23.27887+00:00
-- url     : https://prove2.me/theorems/32553170-7edb-4b86-83fb-b5f8c7a1be5d
-- title:
--   Claim 4.6 — levels $m<\ell$: $\Delta_m\le0$ and $\min\{\varepsilon_{\ell-1},1/2\}\le-\sum_{m<\ell}\frac{3^{\ell-m-1}}{w_m}\Delta_m$
-- statement:
--   Let $x$, $Y$, $r$, an augmenting chain $M_0,\dots,M_k$ and the level $\ell$ be as in Claim 4.4, and suppose $d_i=d(x_i,r)>0$ for all $i<\ell$. Then:
--
--   1. $\Delta_m\le0$ for every $1\le m<\ell$;
--   2. $$\min\{\varepsilon_{\ell-1},1/2\}\le-\sum_{m=1}^{\ell-1}\frac{3^{\ell-m-1}}{w_m}\,\Delta_m .$$
--
--   A weighted sum of the matching-cost decreases at the levels below $\ell$ bounds the capped value of $\varepsilon_{\ell-1}$, which compensates the loss in Claim 4.4.
--
--   **Formalization Note** $w_m$ is `weight (m - 1)`; the sum runs over `Finset.Icc 1 (ℓ - 1)` and is empty when $\ell=1$.
--
--   Differences from the source:
--   - generalization: §4.2 assumes d_i > 0 for all 1 ≤ i ≤ k → d_i > 0 only for the ranks i < ℓ; reason: the proof uses only these distances, and Lemmas 4.7–4.8 apply the claim this way to a truncated list ("applying the calculation until j − 1", PDF p. 14)
--   - encoding: the fixed optimal matchings M_m built by successive augmentation, and ℓ the first index with y_ℓ = r → any augmenting chain M (IsAugmentingChain) and ℓ characterised by IsFirstUse; reason: the paper's chain is an arbitrary such chain; with nested images, the first level whose matching uses a taxi at r is the first index with y_ℓ = r
--   - encoding: ε_m := min{ε ≥ 0 : C_m(T) ≤ εT for every T > 0} → sInf of the same set; reason: under the positivity hypotheses the set is nonempty, closed and bounded below, so the infimum is the minimum
--   - encoding: 1-based ranks i = 1, …, k → 0-based slots j : Fin k (rank j + 1); levels m : ℕ count leading slots; reason: Lean convention; same instances
--   - generalization: k ≥ 2 (standing assumption, PDF p. 4) → k ≥ 1, including the one-taxi case; reason: the statement also holds for one taxi and specializes to every k ≥ 2; at k = 1 the scan is the identity, the matching has one edge, and any lower-level sum is empty
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Claim 4.6, PDF p. 13 (printed p. 12)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Analysis

namespace KTaxi.Competitive

/-- **Claim 4.6** (levels `m < ℓ`; PDF p. 12). Let `M` be an augmenting chain for `x` and `Y`,
and `ℓ` the first level whose matching uses `r`, with `d_i > 0` for all slots `i < ℓ - 1`
(ranks `< ℓ`). Then `Δ_m ≤ 0` for every `1 ≤ m < ℓ`, and
`min{ε_{ℓ-1}, 1/2} ≤ - ∑_{m=1}^{ℓ-1} (3^{ℓ-m-1} / w_m) Δ_m`
(`w_m`, the weight of rank `m`, is `weight (m - 1)`). -/
theorem claim_4_6 {V : Type*} [MetricSpace V] {k : ℕ} (x Y : Fin k → V) (r : V)
    (M : ℕ → Fin k → Fin k) (hM : IsAugmentingChain x Y M) (ℓ : ℕ) (hℓ : IsFirstUse Y r M ℓ)
    (hpos : ∀ i : Fin k, i.val + 1 < ℓ → 0 < dist (x i) r) :
    (∀ m, 1 ≤ m → m < ℓ → levelDelta x Y r m ≤ 0) ∧
    min (epsLevel x Y r M (ℓ - 1)) (1 / 2) ≤
      -∑ m ∈ Finset.Icc 1 (ℓ - 1), (3 : ℝ) ^ (ℓ - m - 1) / weight (m - 1) * levelDelta x Y r m := by sorry

end KTaxi.Competitive
