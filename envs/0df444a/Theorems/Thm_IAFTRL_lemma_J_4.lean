-- Prove2me | Theorems.Thm_IAFTRL_lemma_J_4
-- name    : IAFTRL.lemma_J_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:45:50.889474+00:00
-- url     : https://prove2.me/theorems/5bc267b3-2894-4fb8-8937-6cb2aa920dc1
-- title:
--   Lemma J.4 — centered exponential bound for the proxy function
-- statement:
--   Let $\chi(x)=e^x+e^{-x}-2$. Then $\chi$ is
--   1. even: $\chi(-x)=\chi(x)$;
--   2. convex on $\mathbb R$;
--   3. nonnegative;
--   4. increasing in $|x|$: $|x|\le|y|$ implies $\chi(x)\le\chi(y)$;
--
--   and for every real $x$,
--   $$
--   e^x-x-1\le\chi(x),\qquad \chi(x)\le x^2e^{|x|},\qquad \chi(x)\le\tfrac32x^2\ \ (|x|\le1).
--   $$
--   Moreover, for every probability measure $q$ and every bounded measurable function $f$,
--   $$
--   \int\chi\Big(f-\int f\,dq\Big)\,dq\le\int\chi(2f)\,dq. \tag{J.6}
--   $$
--
--   These inequalities convert the program's proxy function into a bound on the FTRL mixability gap (Lemmas D.4 and D.10).
--
--   Differences from the source:
--   - encoding: "increasing in $|x|$" → $|x|\le|y|\Rightarrow\chi(x)\le\chi(y)$; reason: the standard meaning; same content
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix J.1, Lemma J.4, p.206, Eq. (J.6)

import Mathlib
import Definitions.Def_IAFTRL_chi

namespace IAFTRL

open MeasureTheory

/-- **Lemma J.4 (Centered exponential bound for the proxy function).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma J.4, p.206:
"Let `χ(x) = e^x + e^{−x} − 2`. It is even, convex, nonnegative, and increasing in `|x|`. For every
real `x`, `e^x − x − 1 ≤ χ(x)`, `χ(x) ≤ x²e^{|x|}`, `χ(x) ≤ 3/2 x² (|x| ≤ 1)`. For every probability
measure `q` and bounded measurable `f`, `∫ χ(f − ∫ f dq) dq ≤ ∫ χ(2f) dq`. (J.6)"

The function `χ(x) = e^x + e^{−x} − 2` is
1. even, 2. convex on `ℝ`, 3. nonnegative, 4. increasing in `|x|` (`|x| ≤ |y| ⇒ χ(x) ≤ χ(y)`),
and satisfies
5. `e^x − x − 1 ≤ χ(x)`, 6. `χ(x) ≤ x² e^{|x|}` for every real `x`,
7. `χ(x) ≤ (3/2)x²` for `|x| ≤ 1`,
8. (J.6) `∫ χ(f − ∫ f dq) dq ≤ ∫ χ(2f) dq` for every probability measure `q` and every bounded
   measurable real function `f`. -/
theorem lemma_J_4 :
    (∀ x : ℝ, chi (-x) = chi x) ∧ ConvexOn ℝ Set.univ chi ∧ (∀ x : ℝ, 0 ≤ chi x) ∧
    (∀ x y : ℝ, |x| ≤ |y| → chi x ≤ chi y) ∧
    (∀ x : ℝ, Real.exp x - x - 1 ≤ chi x) ∧ (∀ x : ℝ, chi x ≤ x ^ 2 * Real.exp |x|) ∧
    (∀ x : ℝ, |x| ≤ 1 → chi x ≤ 3 / 2 * x ^ 2) ∧
    (∀ {X : Type*} [MeasurableSpace X] (q : Measure X) [IsProbabilityMeasure q] (f : X → ℝ),
      Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
      ∫ x, chi (f x - ∫ y, f y ∂q) ∂q ≤ ∫ x, chi (2 * f x) ∂q) := by sorry

end IAFTRL
