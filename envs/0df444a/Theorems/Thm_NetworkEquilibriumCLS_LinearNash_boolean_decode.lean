-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_boolean_decode
-- name    : NetworkEquilibriumCLS.LinearNash.boolean_decode
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:33.458584+00:00
-- url     : https://prove2.me/theorems/993211be-556c-4929-9125-fbb9efa72864
-- title:
--   Lemma 4.4 — Boolean controls give all-flip local minimality
-- statement:
--   Let v=(x,y,s,s′) be a real box KKT point of the Section 4 potential Φ, with positive dimensions, normalized rational p and integer h. If every average control is Boolean, then
--
--   $$b=(\bar s_q)_q\in\{0,1\}^n,\qquad h(b)\le h(b\oplus q)\quad\text{for every }q.$$
--
--   This is local minimality under every single-bit flip, rather than global optimality or a restriction on selected flips. It supplies the second alternative for exact recovery through the Boolean decoder.
--
--   Differences from the source:
--   - encoding: positive dimensions and indices 1 through d → Fin d with d positive and indices 0 through d-1; reason: a bijective relabelling; all real-cube coordinates and all boundary cases are retained
--   - generalization: h obtained from the Boolean local-search reduction for p → any integer square-free quadratic h of positive dimension; reason: the analytic proof uses only integer coefficients, the row-sum bound, and the stated polynomial; taking the h supplied by Lemma 3.2 recovers the source
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.13 (PDF 14), Lemma 4.4.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Potential

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem boolean_decode :
    ∀ (m n : ℕ), 0 < m → 0 < n →
    ∀ (p : Quadratic m) (h : BooleanPolynomial n) (v : Coordinate m n → ℝ),
      IsNormalized p → FunctionKKT (potential p h) v →
      (∀ q, controlAverage v q = 0 ∨ controlAverage v q = 1) →
      BooleanLocalMin h (controlAverage v) := by sorry

end NetworkEquilibriumCLS.LinearNash
