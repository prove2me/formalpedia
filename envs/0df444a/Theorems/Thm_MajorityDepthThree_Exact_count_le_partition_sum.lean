-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_count_le_partition_sum
-- name    : MajorityDepthThree.Exact.count_le_partition_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:34.995023+00:00
-- url     : https://prove2.me/theorems/076b652a-76c3-403e-884b-6bdd0f6a29cf
-- title:
--   Fact 4.2 — threshold count and weighted minimal sets
-- statement:
--   Let $F$ be a $t$-threshold CNF on a finite ground set $V$ and let $R>0$ be real. With $\theta_t(F)$ the number of weight-$t$ satisfying sets and $Z(F,R)=\sum_{U\in M(F)}R^{|U|}$,
--
--   $$\theta_t(F)\le R^{-t}Z(F,R).$$
--
--   The claim applies to signed formulas of arbitrary width and retains arbitrary positive $R$. It relates the boundary-layer count to the weighted sum used by the LP reduction.
--
--   Differences from the source:
--   - encoding: A finite ground set V and its subsets → Finite subsets V of a variable type, with finite families of subsets; reason: Every source instance has this representation; all assignments and ambient isolated variables are retained
--   - generalization: Section 4 fixes F to be a 3-CNF → The weighted counting inequality is stated for valid CNFs of arbitrary width; reason: Every satisfying set of weight t is inclusion-minimal under the threshold hypothesis, independent of clause width; specializing to width three recovers Fact 4.2
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.11, Fact 4.2 and preceding definition of Z

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem count_le_partition_sum {α : Type} [DecidableEq α] (V : Finset α)
    (F : CNF α) (t : ℕ) (hv : ValidCNF V F) (ht : Threshold V F t)
    (R : ℝ) (hR : 0 < R) :
    (theta V F t : ℝ) ≤ R ^ (-(t : ℤ)) * partitionSum V F R := by sorry

end MajorityDepthThree.Exact
