-- Prove2me | Theorems.Thm_KTaxi_Competitive_claim_4_5
-- name    : KTaxi.Competitive.claim_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:29:19.730284+00:00
-- url     : https://prove2.me/theorems/9ddd4778-100c-45b2-a0ad-2a5b7fdd3c60
-- title:
--   Claim 4.5 — recurrence $\min\{\varepsilon_m,1/2\}\le3\min\{\varepsilon_{m-1},1/2\}+g_m$
-- statement:
--   Let $x$, $Y$, $r$, an augmenting chain $M_0,\dots,M_k$ and the level $\ell$ be as in Claim 4.4. For every level $1\le m<\ell$ such that $d_i=d(x_i,r)>0$ for all $i\le m$,
--   $$
--   \min\{\varepsilon_m,1/2\}\le3\min\{\varepsilon_{m-1},1/2\}+g_m ,\qquad g_m=\frac{D(X_m,Y)-D(X_{m-1},Y)}{d_m}.
--   $$
--   It bounds how the near-$r$ part of the optimal matchings below level $\ell$ can grow from one level to the next.
--
--   **Formalization Note** The level is written $m=j+1$ with $j$ the 0-based slot of $x_m$; $g_m$ is `gNorm x Y r j`.
--
--   Differences from the source:
--   - generalization: §4.2 assumes d_i > 0 for all 1 ≤ i ≤ k → d_i > 0 only for the ranks i ≤ m; reason: the proof uses only these distances, and Lemmas 4.7–4.8 apply the claim this way to a truncated list ("applying the calculation until j − 1", PDF p. 14)
--   - encoding: the fixed optimal matchings M_m built by successive augmentation, and ℓ the first index with y_ℓ = r → any augmenting chain M (IsAugmentingChain) and ℓ characterised by IsFirstUse; reason: the paper's chain is an arbitrary such chain; with nested images, the first level whose matching uses a taxi at r is the first index with y_ℓ = r
--   - encoding: ε_m := min{ε ≥ 0 : C_m(T) ≤ εT for every T > 0} → sInf of the same set; reason: under the positivity hypotheses the set is nonempty, closed and bounded below, so the infimum is the minimum
--   - encoding: 1-based ranks i = 1, …, k → 0-based slots j : Fin k (rank j + 1); levels m : ℕ count leading slots; reason: Lean convention; same instances
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Claim 4.5, PDF p. 11 (printed p. 10)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Analysis

namespace KTaxi.Competitive

/-- **Claim 4.5** (recurrence on `ε_m`; PDF p. 10). Let `M` be an augmenting chain for `x` and
`Y`, and `ℓ` the first level whose matching uses `r`. For every level `1 ≤ m < ℓ` with
`d_i > 0` for all slots `i < m`, `min{ε_m, 1/2} ≤ 3 min{ε_{m-1}, 1/2} + g_m`.
The level is written `m = j + 1` with `j` the slot of the new taxi `x_m`. -/
theorem claim_4_5 {V : Type*} [MetricSpace V] {k : ℕ} (x Y : Fin k → V) (r : V)
    (M : ℕ → Fin k → Fin k) (hM : IsAugmentingChain x Y M) (ℓ : ℕ) (hℓ : IsFirstUse Y r M ℓ)
    (j : Fin k) (hjℓ : j.val + 1 < ℓ) (hpos : ∀ i : Fin k, i.val ≤ j.val → 0 < dist (x i) r) :
    min (epsLevel x Y r M (j.val + 1)) (1 / 2) ≤
      3 * min (epsLevel x Y r M j.val) (1 / 2) + gNorm x Y r j := by sorry

end KTaxi.Competitive
