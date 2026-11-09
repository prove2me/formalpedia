-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_lemma_B_1
-- name    : OptimalTraceDistance.Estimation.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:36.895146+00:00
-- url     : https://prove2.me/theorems/b454bc51-c9cd-46bd-81fa-2a9c7259b531
-- title:
--   Lemma B.1 — separated Chebyshev differences
-- statement:
--   For integers $k\ge a\ge1$, including repeated nodes, the following functions have finite separated representations with the indicated sum of products of uniform factor bounds:
--   $$T_k^{[a]}:\quad\frac{(2k^2)^a}{(2a)!}\text{ on }[-1,1]^{a+1},\qquad
--   \frac{(4k)^a}{a!}\text{ on }[-1/2,1/2]^{a+1}.$$
--   For each $r\in\{0,a\}$, the order-$a$ divided difference of $x\mapsto T_k(1-x)$ multiplied by $\sqrt{x_r}$ has bound
--   $$\frac{2^ak^{2a-1}}{(2a-1)!}\quad\text{on }[0,1]^{a+1}.$$
--   The separated factors, rather than only the scalar supremum, control ordered matrix products.
--
--   Differences from the source:
--   - encoding: Divided differences including repeated nodes and finite separated representations → Fin (a+1) coordinate vectors, monomial composition sums and explicit uniform factor budgets; reason: The budget condition is equivalent to the source sum of products of supremum norms; no domain or constant changes
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Lemma B.1, p. 28.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem lemma_B_1 (k a : ℕ) (ha : 1 ≤ a) (hk : a ≤ k) :
  HasSeparatedBound a (Set.Icc (-1) 1)
    (dividedDifference (Polynomial.Chebyshev.T ℝ k) a)
    ((2*(k : ℝ)^2)^a / ((2*a).factorial : ℝ)) ∧
  HasSeparatedBound a (Set.Icc (-(1/2)) (1/2))
    (dividedDifference (Polynomial.Chebyshev.T ℝ k) a)
    ((4*(k : ℝ))^a / (a.factorial : ℝ)) ∧
  ∀ r : Fin (a+1), r.val = 0 ∨ r.val = a →
    HasSeparatedBound a (Set.Icc 0 1)
      (fun x => Real.sqrt (x r) * dividedDifference
        ((Polynomial.Chebyshev.T ℝ k).comp (1-Polynomial.X)) a x)
      ((2 : ℝ)^a * (k : ℝ)^(2*a-1) / ((2*a-1).factorial : ℝ)) := by sorry

end OptimalTraceDistance.Estimation
