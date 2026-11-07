-- Prove2me | Theorems.Thm_MeanBudgetXC_lemma_3_7
-- name    : MeanBudgetXC.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:16.343619+00:00
-- url     : https://prove2.me/theorems/58610718-9801-4c47-903b-431e5010c534
-- title:
--   Lemma 3.7 — no additional vertex in a strict rounding chamber
-- statement:
--   Let $2\le d\le N$. Suppose $(x,y)\in R_{N,d}$, $|S|=d$, $x_i>1/2$ for $i\in S$ and $x_j<1/2$ for $j\notin S$. Then either $(x,y)=(\mathbf 1_S,\mathbf 1_{E(S)})$ or $(x,y)$ is not a vertex of $R_{N,d}$.
--
--   Here $\mathbf 1_{E(S)}$ is the indicator of the pairs contained in $S$. With Lemma 3.6 this shows that a vertex above the threshold is an incidence vector.
--
--   Differences from the source:
--   - encoding: The vertex set is $[N]$ → it is an arbitrary finite type $V$ with $N=|V|$; reason: every finite type is in bijection with $[N]$, so no instance changes
--   - encoding: vertex of the polytope $R_{N,d}$ → extreme point (`Set.extremePoints`); reason: for a polytope the two notions coincide
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Lemma 3.7, p.14

import Mathlib
import Definitions.Def_MeanBudgetXC_rltPolytope

namespace MeanBudgetXC

/-- **Lemma 3.7** (No additional vertex in a strict rounding chamber) (Chao–Gao–Qi–Wang, *A Sharp
Mean-Budget Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256
882d9c71…9e76, Section 3.4, p.14). Suppose `(x, y) ∈ R_{N,d}`, `|S| = d`, `x_i > 1/2` for `i ∈ S`
and `x_j < 1/2` for `j ∉ S`. Then either `(x, y) = (1_S, 1_{E(S)})` or `(x, y)` is not a vertex of
`R_{N,d}`.

**Formalization Note** "Vertex" is an extreme point (`Set.extremePoints`); for the polytope
`R_{N,d}` the two notions coincide. `1_{E(S)}` is the indicator of the pairs contained in `S`. The
vertex set is a generic finite type `V` with `N = card V`, and `2 ≤ d ≤ N` is the range of p.13 in
which `R_{N,d}` is used. -/
theorem lemma_3_7 {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd2 : 2 ≤ d)
    (hdN : d ≤ Fintype.card V) (xy : (V → ℝ) × (Pair V → ℝ)) (hxy : xy ∈ rltPolytope V d)
    (S : Finset V) (hS : S.card = d) (hin : ∀ i ∈ S, 1 / 2 < xy.1 i)
    (hout : ∀ j ∉ S, xy.1 j < 1 / 2) :
    xy = ((fun i => if i ∈ S then 1 else 0), fun e => if e.1.toFinset ⊆ S then 1 else 0) ∨
      xy ∉ Set.extremePoints ℝ (rltPolytope V d) := by sorry

end MeanBudgetXC
