-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_Supplement_theorem_7_5
-- name    : MonoABPWidth.Hierarchy.Supplement.theorem_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:38:41.86222+00:00
-- url     : https://prove2.me/theorems/7c4a5dd9-7b23-4eb7-ac84-708f53edd2fa
-- title:
--   Theorem 7.5 — exact permanent optimum
-- statement:
--   Let $n\ge1$ and $d_\times\ge2$ be integers. Define $L(n,1)=n\,n!$ and use all ordered positive compositions in
--   $$L(n,d)=\min_{n=n_1+\cdots+n_\ell\atop\ell\ge1,\ n_i\ge1}\frac{n!}{\prod_i n_i!}\sum_iL(n_i,d-1)\quad(d\ge2).$$
--   There exists a real monotone formula computing $\operatorname{per}_n$ with multiplication depth exactly $d_\times$ and exactly $L(n,d_\times)$ leaves. Every real monotone formula computing that polynomial with the same multiplication depth has at least $L(n,d_\times)$ leaves. Thus the independently defined true optimum equals this recurrence. Both attainment and the universal lower bound are included; the minimum is not restricted to balanced compositions.
--
--   Differences from the source:
--
--   - encoding: positive matrix dimension and minimum over every ordered positive composition → Fin n variables, the complete finite type Composition n, and extended nonnegative leaf counts; reason: the multinomial quotient is exact integer division, all compositions including one part are retained, and unary gates permit exact depth at the degree-one endpoint
--   - generalization: bounded-depth formulas are assumed alternating without loss of generality in §2.3 → the universal lower bound also ranges over nonalternating trees; reason: contracting consecutive gates preserves leaves and never increases multiplication depth; the displayed bound is nonincreasing in depth
--   - encoding: attainment by a bounded-depth formula under the alternating convention of §2.3 → the existential witness is allowed to be any formula tree of the stated exact multiplication depth; reason: contracting adjacent gates preserves leaves and can only reduce multiplication depth; unary alternating gates restore the stated exact multiplication depth without adding leaves, so an alternating witness follows with the same leaf count
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), Theorem 7.5, p.22, PDF23

import Definitions.Def_MonoABPWidth_Hierarchy_Supplement_permanent

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- Theorem 7.5, p.22 (PDF23): exact attainment and universal optimality
of the independent ordered-composition recurrence. -/
theorem theorem_7_5 (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d) :
    (∃ F : Formula (Fin n × Fin n), F.eval = permanent n ∧
      F.mulDepth = d ∧ (F.leaves : ℝ≥0∞) = permanentL n d) ∧
    (∀ F : Formula (Fin n × Fin n), F.eval = permanent n → F.mulDepth = d →
      permanentL n d ≤ (F.leaves : ℝ≥0∞)) := by sorry

end MonoABPWidth.Hierarchy.Supplement
