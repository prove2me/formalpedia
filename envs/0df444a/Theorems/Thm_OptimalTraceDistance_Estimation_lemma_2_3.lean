-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_3
-- name    : OptimalTraceDistance.Estimation.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:07.722328+00:00
-- url     : https://prove2.me/theorems/f84a7c15-b91c-4659-b1e8-f9dc0c1905b5
-- title:
--   Lemma 2.3 — the absolute-value polynomial
-- statement:
--   For every integer $K\ge2$, the real Jackson polynomial $q_K$ from Appendix A.1 is even, has degree at most $K$ and satisfies $q_K(0)=0$. With $C=64$ as established on p.25,
--   $$|q'_K(x)|\le1,\quad|q_K(x)-|x||\le C/K\quad(|x|\le1),$$
--   $$|q_K^{(j)}(x)|\le C^jK^{j-1}\quad(2\le j\le K,\ |x|\le1/2),$$
--   $$\int_{-1}^1|\operatorname{sgn}(x)-q'_K(x)|\,dx\le C/K,\qquad
--   |x|\,|\operatorname{sgn}(x)-q'_K(x)|\le C/K\quad(|x|\le1).$$
--   The loss in the integral is integrable. The same fixed family is used by every later statement.
--
--   Differences from the source:
--   - encoding: Existence of q_K, then the fixed Appendix A.1 family; universal C → The computed Appendix A.1 Chebyshev family, with C=64 and an integrability conclusion; reason: p.25 proves these estimates for this actual family with C=2^6; explicit integrability prevents a default integral value
--   - encoding: Supremum bounds on compact intervals → The same bound holds at every point of each indicated interval; reason: Pointwise upper bounds are equivalent to these supremum inequalities for the actual continuous polynomial derivatives and bounded sign-loss functions
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Lemma 2.3, p. 7.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem lemma_2_3 : ∀ K : ℕ, 2 ≤ K →
  (q K).natDegree ≤ K ∧ (∀ x : ℝ, (q K).eval (-x) = (q K).eval x) ∧
  (q K).eval 0 = 0 ∧
  (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(q K).derivative.eval x| ≤ 1 ∧
    |(q K).eval x - abs x| ≤ 64/(K : ℝ)) ∧
  (∀ j : ℕ, 2 ≤ j → j ≤ K → ∀ x ∈ Set.Icc (-(1/2) : ℝ) (1/2),
    |((Polynomial.derivative^[j]) (q K)).eval x| ≤ (64 : ℝ)^j * (K : ℝ)^(j-1)) ∧
  IntegrableOn (fun x => |sign x - (q K).derivative.eval x|) (Set.Icc (-1 : ℝ) 1) ∧
  (∫ x in (-1 : ℝ)..1, |sign x - (q K).derivative.eval x|) ≤ 64/(K : ℝ) ∧
  (∀ x ∈ Set.Icc (-1 : ℝ) 1,
    |x| * |sign x - (q K).derivative.eval x| ≤ 64/(K : ℝ)) := by sorry

end OptimalTraceDistance.Estimation
