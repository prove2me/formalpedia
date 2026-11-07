-- Prove2me | Theorems.Thm_MinSumClust_lemma_50
-- name    : MinSumClust.lemma_50
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:48:04.332274+00:00
-- url     : https://prove2.me/theorems/b7bd1305-7e9e-460a-aadc-3a73135ac140
-- title:
--   Lemma 50 — every variable of the Erdős–Ko–Rado-type process has $\mathbb E[X_j]\le 3K/(N-M)$
-- statement:
--   Let $0\le N'\le N-1$, $1\le M\le N-N'$, and let $[N'+1:N]$ be split into $M$ nonempty intervals $B_1,\dots,B_M$ from left to right with $l_i=\min B_i$. Let $1\le K\le N-M$ and let $w_{it}\ge 0$ for $t<l_i$. For the random process of Lemma 50 (independent uniform representatives $r_i\in B_i$; a uniform $K$-subset of the non-representatives set to $1$; then, block by block, $X_{r_i}=1$ if another variable of $B_i$ is $1$, else $X_{r_i}=\mathbf 1(\sum_{t<l_i}w_{it}X_t>\frac23\sum_{t<l_i}w_{it})$), every $j$ satisfies
--
--   $$\mathbb E[X_j]\ \le\ 3\cdot\frac{K}{N-M}.$$
--
--   The process mimics Algorithm 6; Lemma 49 follows by taking $X$ to mark the closed $\mathcal S_2$ clusters.
--
--   Differences from the source:
--
--   - encoding: 1-based indices, intervals B_i of [N′+1 : N], weights w_it for t < l_i → 0-based indices, block i = [l_i, l_{i+1}) given by strictly increasing starts with l₀ = N′ and l_i < N; weights given for every t, only t < l_i read and required nonnegative; reason: same processes; E[X_j] is Pr[X_j = 1]
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 50, pp.45–46 (PDF pp.47–48)

import Mathlib
import Definitions.Def_MinSumClust_pexp
import Definitions.Def_MinSumClust_lemma50Process

namespace MinSumClust

/-- **Lemma 50**, pp.45–46 (PDF pp.47–48).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 50, pp.45–46.

Let `N′ ∈ {0} ∪ [N − 1]`, `M ∈ [N − N′]`, the suffix `[N′+1 : N]` split into `M` nonempty intervals
`B₁, …, B_M` from left to right with `l_i = min B_i`, `K ∈ [N − M]`, and nonnegative weights
`w_{it}` for `t < l_i`. For the random process of the lemma (`lemma50Process`), every `j` has
`E[X_j] ≤ 3K/(N − M)`.

**Formalization Note.** Indices are 0-based: block `i` is `[l_i, l_{i+1})` (the last ends at `N`),
`l₀ = N′`, and the starts are strictly increasing and `< N`, which makes the `M` blocks nonempty
intervals partitioning `[N′, N)`. `E[X_j]` is `Pr[X_j = 1]`. -/
theorem lemma_50 (N N' M K : ℕ) (l : Fin M → ℕ) (w : Fin M → Fin N → ℝ) (hN' : N' + 1 ≤ N)
    (hM₁ : 1 ≤ M) (hM₂ : M ≤ N - N') (hl : StrictMono l) (hl₀ : ∀ h : 0 < M, l ⟨0, h⟩ = N')
    (hlN : ∀ i, l i < N) (hK₁ : 1 ≤ K) (hK₂ : K ≤ N - M)
    (hw : ∀ i t, t.val < l i → 0 ≤ w i t) :
    ∀ j : Fin N, pprob (lemma50Process N M K l w) (fun X => X j = true) ≤
      3 * (K : ℝ) / ((N : ℝ) - M) := by sorry

end MinSumClust
