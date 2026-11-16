-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_Supplement_theorem_5_10
-- name    : MonoABPWidth.Hierarchy.Supplement.theorem_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:36:50.229951+00:00
-- url     : https://prove2.me/theorems/531a543b-4479-42e0-8a62-67d14aafd349
-- title:
--   Theorem 5.10 — fixed-depth formula separation
-- statement:
--   For every integer $k\ge2$, there is a real p-family $f$ with polynomial-size monotone formulas of total depth at most $2k$, but no polynomial-size monotone branching programs of width at most $k-1$:
--   $$\exists f\quad f\in\mathrm{mVF}_{2k}\ \land\ f\notin\mathrm{mVBP}_{k-1}.$$
--   The family may depend on $k$. The statement includes $k=2,3$ and compares the full nonuniform classes, with polynomial variable count and degree. It is a companion separation theorem.
--
--   Differences from the source:
--   - encoding: noninclusion of p-family classes → existence of a PolynomialFamily in InMVFDepth (2*k) and outside InMVBP (k-1); reason: class definitions include p-family bounds, actual computations, and uniform polynomial resource constants; finite renaming loses no families
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), Theorem 5.10, p.15, PDF16

import Definitions.Def_MonoABPWidth_Hierarchy_Supplement_families

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- Theorem 5.10, p.15 (PDF16), including k=2 and k=3. -/
theorem theorem_5_10 (k : ℕ) (hk : 2 ≤ k) :
    ∃ f : PolynomialFamily, InMVFDepth (2 * k) f ∧
      ¬ InMVBP (fun _ => k - 1) f := by sorry

end MonoABPWidth.Hierarchy.Supplement
