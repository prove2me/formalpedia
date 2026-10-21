-- Prove2me | Theorems.Thm_ModernOnlineLearning_ParameterFree_lemma_13_6_pointwise
-- name    : ModernOnlineLearning.ParameterFree.lemma_13_6_pointwise
-- status  : Proved
-- author  : @suzukasan
-- created : 2026-10-21T05:31:35.025159+00:00
-- url     : https://prove2.me/theorems/ea467d8d-987e-469f-b595-7573f8ff9b41
-- title:
--   Lemma 13.6, p. 213: pointwise Gaussian exponential conjugate bound
-- statement:
--   Let $a,b>0$ and let $x,y$ be arbitrary real numbers. Then
--
--   $$xy-b\exp\!\left(\frac{x^2}{2a}\right)\le |y|\sqrt{2a\log\!\left(1+\frac{\sqrt a\,|y|}{b}\right)}-b.$$
--
--   This uniform pointwise inequality gives the final upper bound on the Fenchel conjugate of $x\mapsto b\exp(x^2/(2a))$ in Lemma 13.6. It converts an exponential wealth lower bound into a comparator-dependent regret bound.
--
--   **Formalization Note** The statement is the pointwise form of the last conjugate bound, retaining the negative constant $-b$. It does not formalize the preceding exact Lambert-W formula.
-- source:
--   Francesco Orabona, Online Learning: A Modern Introduction Using Convex Optimization, arXiv:1912.13213v10, Lemma 13.6, printed p. 213, final inequality. https://arxiv.org/abs/1912.13213v10

import Mathlib

theorem ModernOnlineLearning.ParameterFree.lemma_13_6_pointwise (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) :
    x * y - b * Real.exp (x ^ 2 / (2 * a)) ≤
      |y| * Real.sqrt (2 * a * Real.log (1 + Real.sqrt a * |y| / b)) - b := by sorry
