-- Prove2me | Theorems.Thm_MasulloRH_double_euler_difference_critical_edge_escape
-- name    : MasulloRH.double_euler_difference_critical_edge_escape
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T10:23:06.645171+00:00
-- url     : https://prove2.me/theorems/d21ed217-b87e-4170-b677-4ded23cf59ab
-- title:
--   Two detwisted translations make a unit edge-moment packet vanish in the critical weighted norm
-- statement:
--   For a normalized twice differentiable packet supported on [-2,-1] with bounded second derivative and nonnegative log shifts a,b, define h_T(x)=exp(x/2)u(x/T)/T. Its left Mellin edge moment equals one, while the full critical weighted squared norm after applying the two fixed detwisted differences tends to zero.
-- source:
--   Masullo critical weight and local Euler factors; native analytic certificate for the two-place obstruction.

import Mathlib
open MeasureTheory Filter Topology Set

theorem MasulloRH.double_euler_difference_critical_edge_escape (u : ℝ → ℝ) (hu : Differentiable ℝ u) (hd : Differentiable ℝ (deriv u))
    (K : ℝ) (hK : 0 ≤ K) (hcurv : ∀ y, |deriv (deriv u) y| ≤ K)
    (hs : ∀ y ∉ Icc (-2:ℝ) (-1), u y = 0) (hm : (∫ y : ℝ, u y) = 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let h := fun T x : ℝ => Real.exp (x/2) * u (x/T) / T
    let D := fun T x : ℝ => h T x - Real.exp (a/2)*h T (x-a)
        - Real.exp (b/2)*h T (x-b) + Real.exp ((a+b)/2)*h T (x-a-b)
    (∀ T : ℝ, 0 < T → (∫ x : ℝ, Real.exp (-x/2)*h T x) = 1) ∧
    Tendsto (fun T : ℝ => ∫ x : ℝ, Real.exp |x| * (1+x^2)^2 * (D T x)^2) atTop (𝓝 0) := by sorry
