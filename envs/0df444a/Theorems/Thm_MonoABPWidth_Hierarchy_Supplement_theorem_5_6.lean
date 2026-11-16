-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_Supplement_theorem_5_6
-- name    : MonoABPWidth.Hierarchy.Supplement.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:35:35.966787+00:00
-- url     : https://prove2.me/theorems/094056b7-f620-45cb-9457-872fd8da7c37
-- title:
--   Theorem 5.6 — IMM leaf lower bound
-- statement:
--   Let $k,n\ge1$, and let $F$ be any arbitrary-fan-in real monotone formula computing $\mathrm{imm}_{k,n}$. Write $d_\times$ for its multiplication depth and $\lambda(F)$ for its leaf count. For $d_\times>0$,
--   $$\lambda(F)\ge n\, k^{d_\times(n^{1/d_\times}-1)}.$$
--   At depth zero the proof extends the bound to $n$ for $n\le1$ and $+\infty$ for $n\ge2$, thereby asserting that no such formula exists in the latter case. No syntactic homogeneity or fixed-depth restriction is imposed. This gives the exact IMM leaf lower bound independently of the retained mABP goal.
--
--   Differences from the source:
--   - encoding: finite variable sets, real nonnegative coefficients, and tree resources → Fin-indexed variables/children, NNReal labels, and recursively computed resources; reason: finite renaming preserves every instance and a scalar-variable leaf still costs one leaf
--   - generalization: bounded-depth formulas are assumed alternating without loss of generality in §2.3 → the universal lower bound also ranges over nonalternating trees; reason: contracting consecutive gates preserves leaves and never increases multiplication depth; the displayed bound is nonincreasing in depth
--   - encoding: positive-depth formula and the proof’s depth-zero extension → ENNReal.ofReal of the positive-depth expression, with an explicit zero-depth branch; reason: avoids interpreting 1/0 as zero and represents the proof’s infinite bound
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), Theorem 5.6, p.14, PDF15

import Definitions.Def_MonoABPWidth_Hierarchy_Supplement_formulas
import Definitions.Def_SetMultCost_imm

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- Theorem 5.6, p.14 (PDF15); depth-zero extension from p.21 (PDF22).
No homogeneity, variable order, perfect-power length or fixed depth is assumed. -/
theorem theorem_5_6 (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (F : Formula (SetMultCost.IMMVar k n)) (hF : F.eval = SetMultCost.imm ℝ k n) :
    immLeafLower k n F.mulDepth ≤ (F.leaves : ℝ≥0∞) := by sorry

end MonoABPWidth.Hierarchy.Supplement
