-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_cancelled_hessian_far_bound
-- name    : HunterPDE.Newtonian.cancelled_hessian_far_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T18:03:31.507986+00:00
-- url     : https://prove2.me/theorems/e49dba20-fbce-4957-aa08-1249028fae13
-- title:
--   Integrated far-field cancelled Newtonian Hessian difference bound
-- statement:
--   Let $n\ge2$ and $0<\alpha<1$, and set $K_{ij}=\partial_{ij}\Gamma$ for the Newtonian fundamental solution. There is $A_{n,\alpha}\ge0$ such that every continuous function with $|f(x)-f(y)|\le H|x-y|^\alpha$, $H\ge0$, satisfies the following. For every midpoint $m$, nonzero vector $h$ and coordinate pair $i,j$, the function
--
--   $$F(z)=[K_{ij}(z+h)-K_{ij}(z-h)][f(m-z)-f(m+h)]$$
--
--   is integrable on $|z|>2|h|$, and
--
--   $$\left|\int_{|z|>2|h|}F(z)\,dz\right|\le A_{n,\alpha}H(2|h|)^\alpha.$$
--
--   This is the integrated kernel-difference term in the far part of the Newtonian Holder estimate. It does not include the remaining constant source-increment times signed kernel term.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed pp. 41-42, Theorem 2.28 proof, equation (2.33) and part (b1). Symmetric midpoint coordinates and integration over the full exterior.

import Theorems.Thm_HunterPDE_Newtonian_secondPartial_difference_le
import Theorems.Thm_HunterPDE_Newtonian_norm_fderiv_secondPartial_le
import Theorems.Thm_MeasureTheory_radial_majorant_exterior_bound
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open MeasureTheory HunterPDE.Newtonian
open scoped NNReal

theorem HunterPDE.Newtonian.cancelled_hessian_far_bound (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Continuous f →
      ∀ H : ℝ≥0, (∀ x y, |f x - f y| ≤ (H : ℝ) * ‖x - y‖ ^ α) →
      ∀ m h : EuclideanSpace ℝ (Fin n), h ≠ 0 → ∀ i j : Fin n,
        IntegrableOn (fun z =>
          (secondPartial (fundamentalSolution n) i j (z + h) -
            secondPartial (fundamentalSolution n) i j (z - h)) *
          (f (m - z) - f (m + h))) (Metric.closedBall 0 (2 * ‖h‖))ᶜ ∧
        |∫ z in (Metric.closedBall 0 (2 * ‖h‖))ᶜ,
          (secondPartial (fundamentalSolution n) i j (z + h) -
            secondPartial (fundamentalSolution n) i j (z - h)) *
          (f (m - z) - f (m + h))| ≤ A * (H : ℝ) * (2 * ‖h‖) ^ α := by sorry
