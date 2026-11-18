-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_preprocessing_accuracy
-- name    : LocalOccupancyIS.Glauber.preprocessing_accuracy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:33:00.520955+00:00
-- url     : https://prove2.me/theorems/d01ced20-5357-453d-bab2-b5fb45439f23
-- title:
--   Quantitative termination and accuracy of rational preprocessing
-- statement:
--   Let $\Delta,t,n$ be natural numbers with $\Delta,t\ge1$ and let $b\ge0$ be rational. Put $s=(b+1)^{1/(2t-1)}$, $D=\log(\Delta/s)$ and $x=sD^{2t-1}$. Assume $D\ge0$, $s\le n$, $D\le n$, $t\le n$ and $x\le\Delta$.
--
--   The actual rational parameter-stage procedure has a first successful positive stage $h$, and
--
--   $$1\le h\le20(n+1)^2+2.$$
--
--   If it returns the integer $q$ and rational endpoints $l,u$, then
--
--   $$l\le x\le u,\qquad u-l\le\frac12,\qquad \left|\frac{l+u}{2}-x\right|\le\frac14,$$
--
--   and
--
--   $$x\le q\le x+2,\qquad1\le q\le\Delta+2.$$
--
--   Every earlier positive stage returns no result. This supplies the deterministic termination and rounding hypotheses needed to apply the fair-bit implementation theorem to the rational-input Glauber procedure.
-- source:
--   Davies and Tan, Large independent sets via neighborhood block dynamics, Glauber dynamics, and local occupancy, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf, Corollary 4 and Remark 1 p.6, Proposition 6, Lemmas 9 and 11, Theorem 2, implementation §§6 pp.19–20; quantitative rounding and parameterStage conventions in the mission BitExecution and GoalInterface definitions.

import Definitions.Def_LocalOccupancyIS_Glauber_GoalInterface

namespace LocalOccupancyIS.Glauber
theorem preprocessing_accuracy (Δ t n : ℕ) (b : ℚ) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t)
    (hb : 0 ≤ b) (hD : 0 ≤ D Δ t (b:ℝ)) (hsn : scale t (b:ℝ) ≤ n)
    (hdn : D Δ t (b:ℝ) ≤ n) (htn : t ≤ n)
    (hX : scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1) ≤ Δ) :
    let x := scale t (b:ℝ)*D Δ t (b:ℝ)^(2*t-1)
    ∃ h q : ℕ, ∃ l u : ℚ, 1 ≤ h ∧ h ≤ 20*(n+1)^2+2 ∧
      (∀ j : ℕ,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none) ∧
      ((parameterStage Δ t b h).run 0).1=some (q,l,u) ∧
      (l:ℝ) ≤ x ∧ x ≤ (u:ℝ) ∧ u-l ≤ 1/2 ∧
      |(((l+u)/2:ℚ):ℝ)-x| ≤ 1/4 ∧ x ≤ q ∧ (q:ℝ) ≤ x+2 ∧ 1 ≤ q ∧ q ≤ Δ+2 := by sorry
end LocalOccupancyIS.Glauber
