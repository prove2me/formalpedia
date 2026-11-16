-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_Supplement_theorem_8_4
-- name    : MonoABPWidth.Hierarchy.Supplement.theorem_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:39:51.378185+00:00
-- url     : https://prove2.me/theorems/3d9fbbac-f18a-4a0d-a6af-15a13ccc4a28
-- title:
--   Theorem 8.4 — narrow mABP construction
-- statement:
--   For integers $k,n\ge1$, $w\ge3$, and every integer $1\le r\le\lfloor(w-1)/2\rfloor$, set
--   $$q=\left\lfloor\frac{w-2}{2r-1}\right\rfloor,\qquad b=\left\lceil\frac{k}{q}\right\rceil.$$
--   There exists a real monotone branching program $A$, with singleton source and sink layers, computing $\mathrm{imm}_{k,n}$ such that
--   $$\operatorname{width}(A)\le w,\qquad \operatorname{depth}(A)\le n\,b^{r(\lceil n^{1/r}\rceil-1)}.$$
--   The parameter range guarantees $q\ge1$. All lengths and matrix dimensions are included, along with $w\ge k$. The depth bound keeps its exact front factor and nested rounding. This companion theorem supplies a width-depth upper tradeoff.
--
--   Differences from the source:
--   - encoding: floor and ceiling divisions and width w → natural floor division for q, real ceiling for b, and width at most w in the full published MABP model; reason: the allowed parameter range gives q≥1 and r≥1, so all denominators are positive; width is an upper bound as in the construction
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), Theorem 8.4, p.25, PDF26

import Definitions.Def_MonoABPWidth_Hierarchy_branchingProgram
import Definitions.Def_SetMultCost_imm

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- Theorem 8.4, p.25 (PDF26): exact nested floor/ceiling construction,
all allowed r, and no w<k restriction. The hypotheses give q≥1. -/
theorem theorem_8_4 (k n w r : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hw : 3 ≤ w) (hr : 1 ≤ r) (hrw : r ≤ (w - 1) / 2) :
    let q := (w - 2) / (2 * r - 1)
    let b := Nat.ceil ((k : ℝ) / (q : ℝ))
    ∃ A : MABP (SetMultCost.IMMVar k n), A.output = SetMultCost.imm ℝ k n ∧
      A.width ≤ w ∧
      A.depth ≤ n * b ^ (r * (Nat.ceil ((n : ℝ) ^ (1 / (r : ℝ))) - 1)) := by sorry

end MonoABPWidth.Hierarchy.Supplement
