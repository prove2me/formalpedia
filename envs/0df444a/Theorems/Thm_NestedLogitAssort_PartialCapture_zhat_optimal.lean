-- Prove2me | Theorems.Thm_NestedLogitAssort_PartialCapture_zhat_optimal
-- name    : NestedLogitAssort.PartialCapture.zhat_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:50:16.731223+00:00
-- url     : https://prove2.me/theorems/7e23f933-2e1a-4163-9e12-81d203d290b4
-- title:
--   The greedy fill $\hat z_i(\epsilon)$ solves the continuous knapsack (11)
-- statement:
--   Consider the nested logit model with a finite set $M$ of nests, each offering the products $N=\{1,\dots,n\}$. Product $j$ of nest $i$ has revenue $r_{ij}$ and preference weight $v_{ij}$; $v_{i0}$ is the preference weight of the no-purchase option inside nest $i$, $v_0$ that of choosing no nest, and $\gamma_i$ is the dissimilarity parameter of nest $i$. For $S\subseteq N$ write $V_i(S)=v_{i0}+\sum_{j\in S}v_{ij}$ and $R_i(S)=\sum_{j\in S}r_{ij}v_{ij}/V_i(S)$ (with $R_i(\emptyset)=0$).
--
--   Assume that all preference weights are nonnegative ($v_0\ge 0$, $v_{i0}\ge 0$, $v_{ij}\ge 0$; zero is allowed), all revenues are nonnegative ($r_{ij}\ge 0$), the products of every nest are sorted by revenue ($r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$), and $0\le\gamma_i\le 1$ for every nest $i$. Let $\hat z_i(\epsilon)$ be the greedy solution of the continuous knapsack (11): among the products with $v_{ij}\le\epsilon$, fill the capacity $\epsilon$ in order of decreasing revenue, each product up to the fraction $1$; set $\hat S_i(\epsilon)=\{j : \hat z_{ij}(\epsilon)=1\}$.
--
--   Then for every nest $i$ and every capacity $\epsilon\ge 0$, $\hat z_i(\epsilon)$ is feasible for (11) and optimal: every $z$ with $\sum_j v_{ij}z_j\le\epsilon$ and $0\le z_j\le\mathbf 1(v_{ij}\le\epsilon)$ satisfies
--
--   $$
--   \sum_{j\in N}r_{ij}v_{ij}z_j\le\sum_{j\in N}r_{ij}v_{ij}\hat z_{ij}(\epsilon).
--   $$
--
--   This is the classical optimality of the ratio-greedy rule for the continuous knapsack, here with utility-to-space ratio $r_{ij}$ and the eligibility bound $z_j\le\mathbf 1(v_{ij}\le\epsilon)$; it identifies $\sum_j r_{ij}v_{ij}\hat z_{ij}(\epsilon)$ with $\hat K_i(\epsilon)$.
--
--   Differences from the source:
--   - encoding: 'we can solve this problem by … filling the knapsack' → zhat is feasible for (11) and its objective value is at least that of every feasible z; reason: this is what it means for ẑ_i(ϵ_i) to be an optimal solution to (11)
--   - reading: r_ij is a revenue; its sign is not stated → hypothesis ∀ i j, 0 ≤ r_ij; reason: revenues are nonnegative in the model; the proof of Theorem 10 uses it (p. 45, x̂ ≥ 0; p. 46, Case 1), and the greedy fill solves (11) only for r ≥ 0. Without it Theorem 10 fails (v0 = 0, one nest, v_10 = 0, γ = 1, r_11 = −1, v_11 = 1: x̂ = −1, ŷ = 0, but V({1})^γ(R({1}) − 2x̂) = 1 > 0)
--   - reading: v0, v_i0, v_ij are preference weights (p. 7 allows v0 = 0, v_i0 = 0 and padding products with v_ij = 0) → hypotheses 0 ≤ v0, ∀ i, 0 ≤ v_i0, ∀ i j, 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the paper's remarks on p. 7 allow exactly the zero values
--   - encoding: ẑ_i(ϵ_i): an optimal solution to (11) obtained by sorting by revenue and filling the knapsack → closed-form greedy zhat filling eligible products (v_ij ≤ ϵ) in index order; a zero-weight product gets 1; reason: products are already sorted by revenue (p. 7); ties are filled in index order, which is one solution obtained in this fashion
--   - encoding: products N = {1, …, n}, nests M = {1, …, m} → products Fin n (index 0 is product 1), nests a Fintype M; r_i1 ≥ … ≥ r_in is Antitone (r i); reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, pp. 23–24 (unnumbered)

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_Feas11
import Definitions.Def_NestedLogitAssort_PartialCapture_zhat

namespace NestedLogitAssort.PartialCapture

/-- **The greedy fill solves the continuous knapsack (11).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, pp. 23–24 (unnumbered): "we can solve this problem by sorting the products with respect to
their revenues and filling the knapsack starting from the product with the largest revenue, as
long as we only consider the products whose preference weights do not exceed `ϵ_i`."

For every nest `i` and every `ϵ ≥ 0`, `ẑ_i(ϵ)` is feasible for (11) and its objective value
`∑_j r_{ij} v_{ij} ẑ_{ij}(ϵ)` is at least that of every feasible `z`.

**Formalization Note.** Hypotheses: `v_0, v_{i0}, v_{ij} ≥ 0` (weights, p. 7; zero allowed);
`r_{ij} ≥ 0` (revenues; implicit in the paper and used by its proof of Theorem 10, pp. 45–46);
`r_{i1} ≥ … ≥ r_{in}` (`Antitone`, p. 7); `γ_i ≥ 0` (p. 7) and `γ_i ≤ 1` (Section 5 standing
assumption, p. 22). -/
theorem zhat_optimal {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγ1 : ∀ i, I.γ i ≤ 1)
    (i : M) (ε : ℝ) (hε : 0 ≤ ε) :
    Feas11 I i ε (zhat I i ε) ∧
      ∀ z : Fin n → ℝ, Feas11 I i ε z →
        ∑ j, I.r i j * I.v i j * z j ≤ ∑ j, I.r i j * I.v i j * zhat I i ε j := by sorry

end NestedLogitAssort.PartialCapture
