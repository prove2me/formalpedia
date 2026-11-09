-- Prove2me | Theorems.Thm_NetworkEquilibriumCLS_LinearNash_controls_agree
-- name    : NetworkEquilibriumCLS.LinearNash.controls_agree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:37.957216+00:00
-- url     : https://prove2.me/theorems/6a630b3b-4f8b-46cb-887a-8198c47b3c46
-- title:
--   Lemma 4.2 — both controls agree with their average
-- statement:
--   Let Φ be the Section 4 polynomial for positive dimensions, normalized rational p, and integer square-free quadratic h. At every real box KKT point of Φ, each pair of controls agrees, including its average:
--
--   $$s_q=s'_q=\bar s_q\qquad\text{for every }q.$$
--
--   The conclusion covers boundary and interior controls and both scalar coordinates independently. It gives the common control value used in the fractional and Boolean cases.
--
--   Differences from the source:
--   - encoding: positive dimensions and indices 1 through d → Fin d with d positive and indices 0 through d-1; reason: a bijective relabelling; all real-cube coordinates and all boundary cases are retained
--   - generalization: h obtained from the Boolean local-search reduction for p → any integer square-free quadratic h of positive dimension; reason: the analytic proof uses only integer coefficients, the row-sum bound, and the stated polynomial; taking the h supplied by Lemma 3.2 recovers the source
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.12 (PDF 13), Lemma 4.2.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Potential

namespace NetworkEquilibriumCLS.LinearNash

/-- Source and every encoding convention are recorded in the item metadata. -/
theorem controls_agree :
    ∀ (m n : ℕ), 0 < m → 0 < n →
    ∀ (p : Quadratic m) (h : BooleanPolynomial n) (v : Coordinate m n → ℝ),
      IsNormalized p → FunctionKKT (potential p h) v →
      ∀ q, controlS v q = controlT v q ∧ controlT v q = controlAverage v q := by sorry

end NetworkEquilibriumCLS.LinearNash
