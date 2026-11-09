-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_lemma_A_1
-- name    : LocalProbeMIS871.Greedy.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T01:52:19.058206+00:00
-- url     : https://prove2.me/theorems/85f649de-aa0b-4566-ae2d-dfb8e8b22bde
-- title:
--   Lemma A.1 — Bounds on the fifth-moment coefficients
-- statement:
--   Consider the deterministic coefficient integrals from Eq.(30); this item has no graph or probability parameters.
--
--   Let
--
--   $$u_5=5\int_0^1\frac{z^4\ln(1/z)}{\ln(1+4z)}\,dz,\qquad w_5=5\int_0^1\frac{z^4\ln^2(1/z)}{\ln(1+4z)}\,dz.$$
--
--   Both integrands are integrable on $(0,1)$, and
--
--   $$0<u_5<\frac15,\qquad \ln4-1-5w_5\ge\frac1{160}.$$
--
--   These are the two coefficient estimates used at exponent five, with the printed constants unchanged.
--
--   Differences from the source:
--   - encoding: the two finite integrals displayed in Lemma A.1 → the Eq.(30) coefficient functions at s=5 together with integrability conclusions; reason: real-power exponent 5-1 equals 4 on (0,1); endpoint values do not affect Lebesgue integration and integrability prevents junk values
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 37, PDF p. 39, Lemma A.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Coefficients

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Lemma A.1, printed p.37 / PDF39: both coefficient inequalities. -/
theorem lemma_A_1 :
    IntegrableOn (uIntegrand 5) (Set.Ioo (0 : ℝ) 1) ∧
    IntegrableOn (wIntegrand 5) (Set.Ioo (0 : ℝ) 1) ∧
    (0 < coeffU 5 ∧ coeffU 5 < 1 / 5) ∧
    1 / 160 ≤ Real.log 4 - 1 - 5 * coeffW 5 := by sorry

end LocalProbeMIS871.Greedy
