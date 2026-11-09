-- Prove2me | Theorems.Thm_KTaxi_Competitive_claim_4_4
-- name    : KTaxi.Competitive.claim_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:29:25.420649+00:00
-- url     : https://prove2.me/theorems/a9773059-b965-4a1f-9e4a-0548e85b1fe5
-- title:
--   Claim 4.4 — levels $m\ge\ell$: $\Delta_m\le3^{m-1}-2(1-\min\{\varepsilon_{\ell-1},1/2\})w_\ell$
-- statement:
--   Let $x$ be the online ordered list, $Y$ an adversary configuration, $r$ the pickup, $M_0,\dots,M_k$ an augmenting chain for $x$ and $Y$, and $\ell$ the first level whose matching uses an adversary taxi at $r$. For every level $\ell\le m\le k$ such that $d_i=d(x_i,r)>0$ for all $i\le m$,
--   $$
--   \Delta_m\le3^{m-1}-2\bigl(1-\min\{\varepsilon_{\ell-1},1/2\}\bigr)w_\ell ,
--   $$
--   where $\Delta_m=\sum_{i\le m}\frac{w_i}{d_i}\Delta_{m,i}$ and $\varepsilon_{\ell-1}$ is computed from $M_{\ell-1}$.
--
--   At each level $m\ge\ell$ some taxi of rank at least $\ell$ decreases the level-$m$ matching cost by nearly its distance to $r$ when the edges of $M_{\ell-1}$ near $r$ are short.
--
--   **Formalization Note** $w_\ell$ is `weight (ℓ - 1)` (slot $\ell-1$).
--
--   Differences from the source:
--   - generalization: §4.2 assumes d_i > 0 for all 1 ≤ i ≤ k → d_i > 0 only for the ranks i ≤ m; reason: the proof uses only these distances, and Lemmas 4.7–4.8 apply the claim this way to a truncated list ("applying the calculation until j − 1", PDF p. 14)
--   - encoding: the fixed optimal matchings M_m built by successive augmentation, and ℓ the first index with y_ℓ = r → any augmenting chain M (IsAugmentingChain) and ℓ characterised by IsFirstUse; reason: the paper's chain is an arbitrary such chain; with nested images, the first level whose matching uses a taxi at r is the first index with y_ℓ = r
--   - encoding: ε_m := min{ε ≥ 0 : C_m(T) ≤ εT for every T > 0} → sInf of the same set; reason: under the positivity hypotheses the set is nonempty, closed and bounded below, so the infimum is the minimum
--   - encoding: 1-based ranks i = 1, …, k → 0-based slots j : Fin k (rank j + 1); levels m : ℕ count leading slots; reason: Lean convention; same instances
--   - generalization: k ≥ 2 (standing assumption, PDF p. 4) → k ≥ 1, including the one-taxi case; reason: the statement also holds for one taxi and specializes to every k ≥ 2; at k = 1 the scan is the identity, the matching has one edge, and any lower-level sum is empty
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Claim 4.4, PDF p. 10 (printed p. 9); proof PDF p. 11

import Mathlib
import Definitions.Def_KTaxi_Competitive_Analysis

namespace KTaxi.Competitive

/-- **Claim 4.4** (levels `m ≥ ℓ`; PDF p. 10, proof p. 11). Let `M` be an augmenting chain for
the ordered list `x` and the adversary configuration `Y`, and let `ℓ` be the first level whose
matching uses `r`. For every level `ℓ ≤ m ≤ k` with `d_i > 0` for all slots `i < m`,
`Δ_m ≤ 3^{m-1} - 2 (1 - min{ε_{ℓ-1}, 1/2}) w_ℓ`
(here `w_ℓ`, the weight of rank `ℓ`, is `weight (ℓ - 1)` of slot `ℓ - 1`). -/
theorem claim_4_4 {V : Type*} [MetricSpace V] {k : ℕ} (x Y : Fin k → V) (r : V)
    (M : ℕ → Fin k → Fin k) (hM : IsAugmentingChain x Y M) (ℓ : ℕ) (hℓ : IsFirstUse Y r M ℓ)
    (m : ℕ) (hℓm : ℓ ≤ m) (hmk : m ≤ k) (hpos : ∀ i : Fin k, i.val < m → 0 < dist (x i) r) :
    levelDelta x Y r m ≤
      3 ^ (m - 1) - 2 * (1 - min (epsLevel x Y r M (ℓ - 1)) (1 / 2)) * weight (ℓ - 1) := by sorry

end KTaxi.Competitive
