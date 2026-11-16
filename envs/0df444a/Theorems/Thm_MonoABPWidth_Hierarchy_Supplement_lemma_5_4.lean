-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_Supplement_lemma_5_4
-- name    : MonoABPWidth.Hierarchy.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:36:08.295472+00:00
-- url     : https://prove2.me/theorems/fc414b47-de74-435e-b487-9a386fbcead0
-- title:
--   Lemma 5.4 — IMM formula construction
-- statement:
--   For integers $k\ge2$, $n\ge1$ and $d_+\ge1$, there exists an alternating arbitrary-fan-in real monotone formula $F$ computing $\mathrm{imm}_{k,n}$ with an addition gate at its root, addition depth exactly $d_+$, and
--   $$\lambda(F)=n\,k^{d_+(\lceil n^{1/d_+}\rceil-1)}.$$
--   The front factor is the original $n$, including when $n$ is not a perfect power. This construction supports Theorem 5.10 and is not a step in the proof of the retained goal.
--
--   Differences from the source:
--   - encoding: finite variable sets, real nonnegative coefficients, and tree resources → Fin-indexed variables/children, NNReal labels, and recursively computed resources; reason: finite renaming preserves every instance and a scalar-variable leaf still costs one leaf
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), Lemma 5.4, p.14, PDF15

import Definitions.Def_MonoABPWidth_Hierarchy_Supplement_formulas
import Definitions.Def_SetMultCost_imm

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- Lemma 5.4, p.14 (PDF15): exact leaf count, exact addition depth,
and an addition root, including the non-perfect-power lengths. -/
theorem lemma_5_4 (k n d : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    ∃ F : Formula (SetMultCost.IMMVar k n), F.eval = SetMultCost.imm ℝ k n ∧
      F.Alternating ∧ F.addDepth = d ∧ F.leaves = immLeafUpper k n d ∧ F.addRoot := by sorry

end MonoABPWidth.Hierarchy.Supplement
