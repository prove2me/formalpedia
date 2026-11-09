-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_fractional_decode
-- name    : NetworkEquilibriumCLS.LinearNash.fractional_decode
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:38.103195+00:00
-- url     : https://prove2.me/theorems/01e101ab-0222-4b6c-b248-26310033c9c1
-- title:
--   Lemma 4.3 — a fractional block recovers exact source KKT
-- statement:
--   Let v=(x,y,s,s′) be any real box KKT point of the Section 4 potential Φ, with positive dimensions, |Q_{ii}|≤1 and integer h. For each block q whose average control is strictly between zero and one,
--
--   $$0<\bar s_q<1\quad\Longrightarrow\quad x_q=y_q=z_q\ \text{ and }\ z_q\text{ is an exact KKT point of }p.$$
--
--   Both copy agreements and the exact source KKT conclusion are retained. The source point may be on the boundary of its unit box; only the chosen control is required to be interior. This is the fractional decoding conclusion.
--
--   Differences from the source:
--   - encoding: positive dimensions and indices 1 through d → Fin d with d positive and indices 0 through d-1; reason: a bijective relabelling; all real-cube coordinates and all boundary cases are retained
--   - generalization: h obtained from the Boolean local-search reduction for p → any integer square-free quadratic h of positive dimension; reason: the analytic proof uses only integer coefficients, the row-sum bound, and the stated polynomial; taking the h supplied by Lemma 3.2 recovers the source
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.12 (PDF 13), Lemma 4.3.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Potential

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem fractional_decode :
    ∀ (m n : ℕ), 0 < m → 0 < n →
    ∀ (p : Quadratic m) (h : BooleanPolynomial n) (v : Coordinate m n → ℝ),
      IsNormalized p → FunctionKKT (potential p h) v →
      ∀ q, 0 < controlAverage v q → controlAverage v q < 1 →
        copyX v q = copyY v q ∧ copyY v q = averageZ v q ∧
        QuadraticKKT p (averageZ v q) := by sorry

end NetworkEquilibriumCLS.LinearNash
