-- Prove2me | Theorems.Thm_NestedLogitAssort_PartialCapture_K_le_Khat
-- name    : NestedLogitAssort.PartialCapture.K_le_Khat
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:49:45.873525+00:00
-- url     : https://prove2.me/theorems/1b1a5bea-de34-4982-a7ec-1ddae15c1417
-- title:
--   $K_i(\epsilon)\le\hat K_i(\epsilon)$: the continuous knapsack relaxes the 0–1 knapsack
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}$; $v_{i0}$ is the preference weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i$ is the dissimilarity parameter of nest $i$. For $S\subseteq N$ write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$ (with $R_i(\emptyset)=0$).
--
--   Assume that all preference weights are nonnegative ($v_0\ge 0$, $v_{i0}\ge 0$, $v_{ij}\ge 0$; zero is allowed), all revenues are nonnegative ($r_{ij}\ge 0$), the products of every nest are sorted by revenue ($r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$), and $0\le\gamma_i\le 1$ for every nest $i$.
--
--   For a nest $i$ and a capacity $\epsilon\ge 0$ let $K_i(\epsilon)$ be the value of the 0–1 knapsack (9) and $\hat K_i(\epsilon)$ that of its continuous relaxation (11),
--
--   $$
--   \hat K_i(\epsilon)=\max\Bigl\{\sum_{j\in N}r_{ij}v_{ij}z_{j}:\sum_{j\in N}v_{ij}z_{j}\le\epsilon,\ 0\le z_{j}\le\mathbf 1(v_{ij}\le\epsilon)\Bigr\}.
--   $$
--
--   Then
--
--   $$
--   K_i(\epsilon)\le\hat K_i(\epsilon).
--   $$
--
--   This comparison is used in both cases of the proof of Theorem 10.
--
--   Differences from the source:
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis ∀ i j, 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 10 uses it (p. 45, x̂ ≥ 0; p. 46, Case 1), and the greedy fill solves (11) only for r ≥ 0. Without it Theorem 10 fails (v0 = 0, one nest, v_10 = 0, γ = 1, r_11 = −1, v_11 = 1: x̂ = −1, ŷ = 0, but V({1})^γ(R({1}) − 2x̂) = 1 > 0)
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v0 = 0, v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v0, ∀ i, 0 ≤ v_i0, ∀ i j, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the paper's remarks on p. 7 allow exactly the zero values
--   - encoding: K_i(ϵ_i) and K̂_i(ϵ_i) as maxima (9), (11) → sSup of the set of objective values, z ∈ {0,1}^n as a Finset of products; reason: for ϵ ≥ 0 the sets are nonempty and bounded and the maxima are attained, so sSup is the maximum
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; r_i1 ≥ … ≥ r_in is Antitone (r i); reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, p. 23 (unnumbered)

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_K
import Definitions.Def_NestedLogitAssort_PartialCapture_Khat

namespace NestedLogitAssort.PartialCapture

/-- **The continuous knapsack value dominates the 0–1 value.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, p. 23 (unnumbered): "Since problem (11) is a relaxation of problem (9), we have
`K̂_i(ϵ_i) ≥ K_i(ϵ_i)`."

For every nest `i` and every `ϵ ≥ 0`, `K_i(ϵ) ≤ K̂_i(ϵ)`.

**Formalization Note.** Hypotheses: `v_0, v_{i0}, v_{ij} ≥ 0` (weights, p. 7; zero allowed);
`r_{ij} ≥ 0` (revenues; implicit in the paper and used by its proof of Theorem 10, pp. 45–46);
`r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7); `γ_i ≥ 0` (p. 7) and `γ_i ≤ 1` (Section 5 standing
assumption, p. 22). -/
theorem K_le_Khat {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγ1 : ∀ i, I.γ i ≤ 1)
    (i : M) (ε : ℝ) (hε : 0 ≤ ε) :
    K I i ε ≤ Khat I i ε := by sorry

end NestedLogitAssort.PartialCapture
