-- Prove2me | Theorems.Thm_OnDemandCoord_claim_3
-- name    : OnDemandCoord.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:15.150205+00:00
-- url     : https://prove2.me/theorems/a0318802-95ba-4a77-bb8b-cdc5bdc1311a
-- title:
--   Claim 3 (Edmonds 1970): the greedy vector maximizes a linear function over a polymatroid
-- statement:
--   **Claim 3** (Edmonds 1970; p. A6). Let $g$ be a rank function on the subsets of $I=\{1,\dots,n\}$: $g(\emptyset)=0$, $g$ is nondecreasing and submodular. Let $P(g)=\{x\in\mathbb R^n_+:\ \sum_{i\in U}x_i\le g(U)\ \forall U\subseteq I\}$ be its polymatroid. Let $a\in\mathbb R^n$ and a permutation $j$ of $I$ with
--   $$a_{j(1)}\ge a_{j(2)}\ge\dots\ge a_{j(k)}>0\ge a_{j(k+1)}\ge\dots\ge a_{j(n)} .$$
--   Define $x^*_{j(1)}=g(\{j(1)\})$, $x^*_{j(i)}=g(\{j(1),\dots,j(i)\})-g(\{j(1),\dots,j(i-1)\})$ for $2\le i\le k$, and $x^*_{j(i)}=0$ for $i>k$. Then $x^*\in P(g)$ and
--   $$\sum_{i\in I}a_ix_i\le\sum_{i\in I}a_ix^*_i\qquad\text{for all }x\in P(g).$$
--
--   Applied to $g(U)=\mathbb E[\min\{S,\sum_{i\in U}\hat X_i\}]$, it computes the optimal value of the linear program (8).
--
--   **Formalization Note** The rank function and $P(g)$ are the published definitions `Disjunctive.Polymatroids.IsPolymatroidRankFunction` and `PolymatroidP`, with the same conventions as the paper.
--
--   Differences from the source:
--   - encoding: x*_{j(1)} = g({j(1)}) as a separate line → the marginal formula at the first position; reason: g(∅) = 0, so the two agree
--   - encoding: x* maximizes Σ a_i x_i over P(g, Ω) → x* ∈ P(g) and Σ a_i x_i ≤ Σ a_i x*_i for all x ∈ P(g); reason: the definition of a maximizer
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), Claim 3, p. A6 (PDF 38)

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **Claim 3 (Edmonds 1970)**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. A6 (PDF 38). Let `g` be a rank function on the subsets of
`Fin n` and `a ∈ ℝⁿ`, with `a ∘ j` nonincreasing for a permutation `j`, positive at the first `k`
positions and nonpositive at the others. Then the greedy vector maximizes `∑_i a_i x_i` over the
polymatroid `P(g)`.

**Formalization Note.** `P(g)` and "rank function" are the published
`Disjunctive.Polymatroids.PolymatroidP` and `IsPolymatroidRankFunction`. -/
theorem claim_3 {n : ℕ} (g : Finset (Fin n) → ℝ)
    (hg : Disjunctive.Polymatroids.IsPolymatroidRankFunction g)
    (a : Fin n → ℝ) (j : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n)
    (ha : Antitone (a ∘ j))
    (hpos : ∀ l : Fin n, (l : ℕ) < k → 0 < a (j l))
    (hnonpos : ∀ l : Fin n, k ≤ (l : ℕ) → a (j l) ≤ 0) :
    greedyVector g j k ∈ Disjunctive.Polymatroids.PolymatroidP g ∧
      ∀ x ∈ Disjunctive.Polymatroids.PolymatroidP g,
        ∑ i, a i * x i ≤ ∑ i, a i * greedyVector g j k i := by sorry

end OnDemandCoord
