-- Prove2me | Theorems.Thm_OncePaid_Sparse_eq_A_3
-- name    : OncePaid.Sparse.eq_A_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:47:33.642679+00:00
-- url     : https://prove2.me/theorems/06649e6e-b229-409a-bbbf-725b7e334c21
-- title:
--   §A.3, Eq. (A.3) — sparse cut count $B_H(n/40)\le(468/(5e))^n$
-- statement:
--   Let $H$ be as in Theorem 4.1: a simple bipartite graph, $102$-regular, with $n>3$ vertices on each side and all nontrivial biadjacency singular values at most $21$. Then the cut count (3.5) satisfies
--
--   $$
--   B_H(n/40)\ \le\ \Big(\frac{468}{5e}\Big)^n. \tag{A.3}
--   $$
--
--   That is, for every $U\subseteq V_L$, $V\subseteq V_R$ with $|U|=|V|\in[\lceil n/3\rceil,\lfloor2n/3\rfloor]$, at most $(468/(5e))^n$ perfect matchings $M$ have $|M(U)\triangle V|\le n/40$. Compared with the at least $(102/e)^n$ perfect matchings of $H$, this is an exponentially small fraction.
--
--   Differences from the source:
--   - encoding: "all nontrivial biadjacency singular values at most 21" → $\|Bf\|_2^2\le21^2\|f\|_2^2$ for every $f\perp\mathbf 1$ on $V_R$; reason: equivalent for a $102$-regular bipartite host.
--   - encoding: $n$ vertices on each side → $|V_R|=|V_L|=n$; $\lceil n/3\rceil,\lfloor 2n/3\rfloor$ → natural-number divisions $(n+2)/3$, $2n/3$; reason: Lean representation.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 36, App. A.3, Eq. (A.3) (PDF p. 38)

import Mathlib
import Definitions.Def_OncePaid_Sparse_BipHost

namespace OncePaid.Sparse

/-- App. A.3, Eq. (A.3), p. 36. For `H` as in Theorem 4.1 (bipartite, `102`-regular, `n > 3`
vertices on each side, nontrivial biadjacency singular values at most `21`):
`B_H(n/40) ≤ (468/(5e))^n`. -/
theorem eq_A_3 {L R : Type} [Fintype L] [Fintype R] (adj : L → R → Prop)
    (hLR : Fintype.card R = Fintype.card L) (hn : 3 < Fintype.card L)
    (hreg : IsBiregular adj 102) (hspec : NontrivialSingularValuesLe adj 21) :
    (cutCount adj ((Fintype.card L : ℝ) / 40) : ℝ) ≤
      (468 / (5 * Real.exp 1)) ^ (Fintype.card L) := by sorry

end OncePaid.Sparse
