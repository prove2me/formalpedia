-- Prove2me | Theorems.Thm_OncePaid_Sparse_eq_A_2
-- name    : OncePaid.Sparse.eq_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:47:51.815123+00:00
-- url     : https://prove2.me/theorems/e9817d81-e837-4844-b58a-966a94305cdb
-- title:
--   §A.3, Eq. (A.2) — balanced-cut block edges: $e(U,V)+e(U^c,V^c)\le n\{102-162x(1-x)\}\le 66n$
-- statement:
--   Let $H$ be as in Theorem 4.1: a simple bipartite graph, $102$-regular, with $n>3$ vertices on each side, whose biadjacency matrix $B$ has all nontrivial singular values at most $21$ ($\|Bf\|_2\le21\|f\|_2$ whenever $\sum_jf_j=0$). Let $U\subseteq V_L$, $V\subseteq V_R$ with $|U|=|V|=xn$ and $1/3\le x\le2/3$, and let $e(U,V)$ count the edges between $U$ and $V$. Then
--
--   $$
--   e(U,V)\le 102x^2n+21x(1-x)n,
--   $$
--
--   $$
--   e(U,V)+e(U^c,V^c)\ \le\ n\{102-162x(1-x)\}\ \le\ 66n. \tag{A.2}
--   $$
--
--   The bound limits the number of edges inside the two diagonal blocks of a balanced cut, which is what makes few-crossing perfect matchings rare.
--
--   Differences from the source:
--   - encoding: "all nontrivial biadjacency singular values at most 21" → $\|Bf\|_2^2\le21^2\|f\|_2^2$ for every $f\perp\mathbf 1$ on $V_R$; reason: equivalent for a $102$-regular bipartite host ($\mathbf 1$ is a top singular vector and $\mathbf 1^\perp$ is invariant under $B^{\mathsf T}B$).
--   - encoding: $|U|=|V|=xn$ → real $x$ with $|U|=xn$ and $|V|=xn$; $n$ vertices on each side → $|V_R|=|V_L|=n$; reason: Lean representation.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 36, App. A.3, Eq. (A.2) (PDF p. 38)

import Mathlib
import Definitions.Def_OncePaid_Sparse_BipHost

namespace OncePaid.Sparse

/-- App. A.3, Eq. (A.2), p. 36. Let `H` be as in Theorem 4.1: bipartite (simple), `102`-regular,
`n > 3` vertices on each side, all nontrivial biadjacency singular values at most `21`. If
`U ⊆ V_L`, `V ⊆ V_R` and `|U| = |V| = xn` with `1/3 ≤ x ≤ 2/3`, then
`e(U, V) ≤ 102 x² n + 21 x(1 − x) n` and
`e(U, V) + e(Uᶜ, Vᶜ) ≤ n {102 − 162 x(1 − x)} ≤ 66 n`. -/
theorem eq_A_2 {L R : Type} [Fintype L] [Fintype R] (adj : L → R → Prop)
    (hLR : Fintype.card R = Fintype.card L) (hn : 3 < Fintype.card L)
    (hreg : IsBiregular adj 102) (hspec : NontrivialSingularValuesLe adj 21)
    (U : Finset L) (V : Finset R) (x : ℝ)
    (hU : (U.card : ℝ) = x * (Fintype.card L : ℝ)) (hV : (V.card : ℝ) = x * (Fintype.card L : ℝ))
    (hx1 : 1 / 3 ≤ x) (hx2 : x ≤ 2 / 3) :
    (edgesBetween adj U V : ℝ) ≤
        102 * x ^ 2 * (Fintype.card L : ℝ) + 21 * x * (1 - x) * (Fintype.card L : ℝ) ∧
      (edgesBetween adj U V : ℝ) + (edgesOutside adj U V : ℝ) ≤
        (Fintype.card L : ℝ) * (102 - 162 * x * (1 - x)) ∧
      (Fintype.card L : ℝ) * (102 - 162 * x * (1 - x)) ≤ 66 * (Fintype.card L : ℝ) := by sorry

end OncePaid.Sparse
