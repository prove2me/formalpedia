-- Prove2me | Theorems.Thm_MeanBudgetXC_appendix_A_4_dimension_bound
-- name    : MeanBudgetXC.appendix_A_4_dimension_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:38:53.817611+00:00
-- url     : https://prove2.me/theorems/9bb8acd4-66fe-4334-9b50-a862eec50501
-- title:
--   Appendix A.4 — dimension lower bound with unrestricted lifts
-- statement:
--   Suppose a nonempty polytope $P$ has dimension $m\ge1$ and is the affine image of a polyhedron described by $s$ inequalities and arbitrary affine equalities. Then
--   $$s\ge m+1.$$
--   The lift may be unbounded.
--
--   This is the universal lower bound that makes the quadratic formulation optimal in order.
--
--   **Formalization Note** "Polytope with an $s$-inequality lift" is a nonempty bounded set with an extended formulation of size $s$. Dimension is the `finrank` of the vector span.
--
--   Differences from the source:
--   - encoding: a nonempty polytope $P$ that is the affine image of a polyhedron with $s$ inequalities and arbitrary equalities → a nonempty bounded set $K$ with `IsEFOfSize K s`; reason: a set with an extended formulation is a polyhedron, and a bounded one is a polytope, so these are the same objects
--   - encoding: $P$ has dimension $m$ → the finrank of the vector span of $K$ is $m$; reason: this is the dimension of the affine hull
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Appendix A.4, p.39

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity

namespace MeanBudgetXC

open ExtensionComplexity.TSP

/-- **Appendix A.4, dimension lower bound with unrestricted lifts** (Chao–Gao–Qi–Wang, *A Sharp
Mean-Budget Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256
882d9c71…9e76, Appendix A.4, p.39). If a nonempty polytope `P` has dimension `m ≥ 1` and is the
affine image of a polyhedron described by `s` inequalities and arbitrary affine equalities, then
`s ≥ m + 1`. This holds also when the lift is unbounded.

**Formalization Note** "Polytope with an `s`-inequality lift" is a nonempty bounded set `K ⊆ ℝ^ι`
with an extended formulation of size `s` (`IsEFOfSize K s`: `s` inequalities, any number of
equations and auxiliary variables); every such set is a polytope. "Dimension `m`" is the `finrank`
of the vector span of `K` (the dimension of its affine hull). -/
theorem appendix_A_4_dimension_bound {ι : Type*} [Fintype ι] (K : Set (ι → ℝ))
    (hne : K.Nonempty) (hbdd : Bornology.IsBounded K) (m s : ℕ) (hm : 1 ≤ m)
    (hdim : Module.finrank ℝ (vectorSpan ℝ K) = m) (hEF : IsEFOfSize K s) :
    m + 1 ≤ s := by sorry

end MeanBudgetXC
