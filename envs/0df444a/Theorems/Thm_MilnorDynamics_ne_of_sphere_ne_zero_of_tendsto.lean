-- Prove2me | Theorems.Thm_MilnorDynamics_ne_of_sphere_ne_zero_of_tendsto
-- name    : MilnorDynamics.ne_of_sphere_ne_zero_of_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T23:05:30.961478+00:00
-- url     : https://prove2.me/theorems/b3673fd2-5a96-4002-b6a1-b2854fb857bf
-- title:
--   Minimum modulus - a boundary circle bounded away from a value forces the limit to avoid it
-- statement:
--   **Minimum modulus, and the limit contradicts it.** Let $U\subseteq\mathbb C$ be open, let $f_n$ be holomorphic on $U$ and never equal to $c$ on $U$, and suppose $f_n$ converges to $g$ locally uniformly on $U$. Let $z_0\in\mathbb C$ and $r>0$ be such that the closed disc $\overline{D(z_0,r)}$ lies in $U$ and $g-c$ has no zero on its boundary circle. Then
--
--   $$g(z_0)\neq c .$$
--
--   Proof. The function $g-c$ is holomorphic on the disc and nonzero on its boundary circle, which is compact, so $m:=\min_{|z-z_0|=r}|g(z)-c|>0$. On that circle the functions $f_n-c$ converge to $g-c$ uniformly; hence for all large $n$ we have $|f_n-c|>m/2$ there. Each $f_n-c$ is holomorphic and zero-free on the closed disc, so $1/(f_n-c)$ is holomorphic there and the maximum modulus principle bounds its value at the centre by its boundary values: $|f_n(z_0)-c|\ge m/2$ for all large $n$. But $f_n(z_0)\to g(z_0)=c$, which contradicts the lower bound. So $g(z_0)\neq c$.
--
--   This is the analytic half of Hurwitz's theorem for limits: it is the step where holomorphy of the $f_n$ and local uniform convergence are actually used.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; the classical minimum-modulus argument inside Hurwitz's theorem.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem ne_of_sphere_ne_zero_of_tendsto (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ) (c : ℂ) (g : ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({c}ᶜ : Set ℂ))
    (hc : TendstoLocallyUniformlyOn f g atTop U)
    (z0 : ℂ) (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall z0 r ⊆ U)
    (hcirc : ∀ z ∈ Metric.sphere z0 r, g z - c ≠ 0) :
    g z0 ≠ c := by sorry

end MilnorDynamics
