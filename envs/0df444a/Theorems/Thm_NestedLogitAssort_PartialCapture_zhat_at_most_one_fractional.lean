-- Prove2me | Theorems.Thm_NestedLogitAssort_PartialCapture_zhat_at_most_one_fractional
-- name    : NestedLogitAssort.PartialCapture.zhat_at_most_one_fractional
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:50:47.237385+00:00
-- url     : https://prove2.me/theorems/baaa7929-0fba-4e3e-b9fe-9a70dbccb2c7
-- title:
--   The greedy solution $\hat z_i(\epsilon)$ has at most one fractional component
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}$; $v_{i0}$ is the preference weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i$ is the dissimilarity parameter of nest $i$. For $S\subseteq N$ write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$ (with $R_i(\emptyset)=0$).
--
--   Assume that all preference weights are nonnegative ($v_0\ge 0$, $v_{i0}\ge 0$, $v_{ij}\ge 0$; zero is allowed), all revenues are nonnegative ($r_{ij}\ge 0$), the products of every nest are sorted by revenue ($r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$), and $0\le\gamma_i\le 1$ for every nest $i$. Let $\hat z_i(\epsilon)$ be the greedy solution of the continuous knapsack (11): among the products with $v_{ij}\le\epsilon$, fill the capacity $\epsilon$ in order of decreasing revenue, each product up to the fraction $1$; set $\hat S_i(\epsilon)=\{j : \hat z_{ij}(\epsilon)=1\}$.
--
--   Then for every nest $i$ and every capacity $\epsilon\ge 0$, at most one product $j$ has $0<\hat z_{ij}(\epsilon)<1$: if $0<\hat z_{ij}(\epsilon)<1$ and $0<\hat z_{ik}(\epsilon)<1$, then $j=k$.
--
--   This is what allows the proof of Theorem 10 to split into the case of exactly one fractional component (covered by the singleton candidates) and the case of none.
--
--   Differences from the source:
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis ∀ i j, 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 10 uses it (p. 45, x̂ ≥ 0; p. 46, Case 1), and the greedy fill solves (11) only for r ≥ 0. Without it Theorem 10 fails (v0 = 0, one nest, v_10 = 0, γ = 1, r_11 = −1, v_11 = 1: x̂ = −1, ŷ = 0, but V({1})^γ(R({1}) − 2x̂) = 1 > 0)
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v0 = 0, v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v0, ∀ i, 0 ≤ v_i0, ∀ i j, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the paper's remarks on p. 7 allow exactly the zero values
--   - encoding: ẑ_i(ϵ_i): an optimal solution to (11) obtained by sorting by revenue and filling the knapsack → closed-form greedy zhat filling eligible products (v_ij ≤ ϵ) in index order; a zero-weight product gets 1; reason: products are already sorted by revenue (p. 7); ties are filled in index order, which is one solution obtained in this fashion
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; r_i1 ≥ … ≥ r_in is Antitone (r i); reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, p. 24 (unnumbered)

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_zhat

namespace NestedLogitAssort.PartialCapture

/-- **The greedy solution has at most one fractional component.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, p. 24 (unnumbered): "We observe that `ẑ_i(ϵ_i)` has at most one fractional component."

For every nest `i` and every `ϵ ≥ 0`, any two indices `j, k` with `0 < ẑ_{ij}(ϵ) < 1` and
`0 < ẑ_{ik}(ϵ) < 1` coincide.

**Formalization Note.** Hypotheses: `v_0, v_{i0}, v_{ij} ≥ 0` (weights, p. 7; zero allowed);
`r_{ij} ≥ 0` (revenues; implicit in the paper and used by its proof of Theorem 10, pp. 45–46);
`r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7); `γ_i ≥ 0` (p. 7) and `γ_i ≤ 1` (Section 5 standing
assumption, p. 22). -/
theorem zhat_at_most_one_fractional {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγ1 : ∀ i, I.γ i ≤ 1)
    (i : M) (ε : ℝ) (hε : 0 ≤ ε) (j k : Fin n)
    (hj0 : 0 < zhat I i ε j) (hj1 : zhat I i ε j < 1)
    (hk0 : 0 < zhat I i ε k) (hk1 : zhat I i ε k < 1) :
    j = k := by sorry

end NestedLogitAssort.PartialCapture
