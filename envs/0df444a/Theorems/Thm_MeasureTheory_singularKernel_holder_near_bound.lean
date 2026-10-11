-- Prove2me | Theorems.Thm_MeasureTheory_singularKernel_holder_near_bound
-- name    : MeasureTheory.singularKernel_holder_near_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:02:35.920777+00:00
-- url     : https://prove2.me/theorems/7fa928b9-9e22-481c-b1f7-1862fc13ee0d
-- title:
--   Near-singularity bound for a kernel with a Holder vanishing factor
-- statement:
--   Let $n\ge1$, $\alpha>0$, and let $K,g:\mathbb R^n\to\mathbb R$ be Lebesgue measurable up to null sets. Suppose $C,H\ge0$, $|K(z)|\le C\|z\|^{-n}$ for $z\ne0$, and $|g(z)|\le H\|z\|^\alpha$ for every $z$. For every $R>0$, the product $Kg$ is integrable on $B_R(0)$ and
--
--   $$\left|\int_{B_R(0)}K(z)g(z)\,dz\right|\le\frac{n|B_1(0)|CH}{\alpha}R^\alpha.$$
--
--   In applications $g(z)$ is an increment of a Holder-continuous source. No differentiability or compact-support hypothesis is needed for this local estimate.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed p. 41, Theorem 2.28 proof, part (a). Generalized measurable-kernel version of the individual near-singularity estimate.

import Theorems.Thm_MeasureTheory_integral_norm_rpow_ball
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Metric
set_option autoImplicit false

theorem MeasureTheory.singularKernel_holder_near_bound (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α)
    (K g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hKm : AEStronglyMeasurable K volume) (hgm : AEStronglyMeasurable g volume)
    (C H : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hK : ∀ z, z ≠ 0 → ‖K z‖ ≤ C * ‖z‖ ^ (-(n : ℝ)))
    (hg : ∀ z, |g z| ≤ H * ‖z‖ ^ α) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z => K z * g z) (ball 0 R) ∧
      |∫ z in ball 0 R, K z * g z| ≤
        (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
          C * H * R ^ α / α := by sorry
