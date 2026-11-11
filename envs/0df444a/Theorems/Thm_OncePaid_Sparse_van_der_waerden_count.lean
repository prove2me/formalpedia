-- Prove2me | Theorems.Thm_OncePaid_Sparse_van_der_waerden_count
-- name    : OncePaid.Sparse.van_der_waerden_count
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:47:48.777387+00:00
-- url     : https://prove2.me/theorems/a88cdb5e-c89b-47c8-915e-7640fc1af89c
-- title:
--   §A.3, van der Waerden count — at least $102^nn!/n^n\ge(102/e)^n$ perfect matchings
-- statement:
--   Let $H$ be as in Theorem 4.1: a simple bipartite graph, $102$-regular, with $n>3$ vertices on each side and all nontrivial biadjacency singular values at most $21$. Then the number of perfect matchings of $H$ satisfies
--
--   $$
--   |\mathcal M(H)|\ \ge\ \frac{102^n\,n!}{n^n}\ \ge\ \Big(\frac{102}{e}\Big)^n .
--   $$
--
--   The first inequality is the van der Waerden permanent theorem for the doubly stochastic matrix $A_H/102$; the count is the denominator against which the cut count (A.3) is compared.
--
--   Differences from the source:
--   - encoding: perfect matchings → bijections $M:V_L\to V_R$ with $iM(i)\in E$, counted as a finset; nontrivial singular values $\le21$ → $\|Bf\|_2^2\le21^2\|f\|_2^2$ for $f\perp\mathbf 1$; $n$ vertices on each side → $|V_R|=|V_L|=n$; reason: Lean representation, equivalent for a $102$-regular bipartite host.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 36, App. A.3, van der Waerden count (PDF p. 38)

import Mathlib
import Definitions.Def_OncePaid_Sparse_BipHost

namespace OncePaid.Sparse

/-- App. A.3, van der Waerden count, p. 36. For `H` as in Theorem 4.1 (bipartite, `102`-regular,
`n > 3` vertices on each side, nontrivial biadjacency singular values at most `21`), `H` has at
least `102^n n!/n^n ≥ (102/e)^n` perfect matchings. -/
theorem van_der_waerden_count {L R : Type} [Fintype L] [Fintype R] (adj : L → R → Prop)
    (hLR : Fintype.card R = Fintype.card L) (hn : 3 < Fintype.card L)
    (hreg : IsBiregular adj 102) (hspec : NontrivialSingularValuesLe adj 21) :
    (102 : ℝ) ^ (Fintype.card L) * (Nat.factorial (Fintype.card L) : ℝ) /
        (Fintype.card L : ℝ) ^ (Fintype.card L) ≤ ((perfectMatchings adj).card : ℝ) ∧
      (102 / Real.exp 1) ^ (Fintype.card L) ≤
        (102 : ℝ) ^ (Fintype.card L) * (Nat.factorial (Fintype.card L) : ℝ) /
          (Fintype.card L : ℝ) ^ (Fintype.card L) := by sorry

end OncePaid.Sparse
