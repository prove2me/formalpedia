-- Prove2me | Theorems.Thm_MasulloRH_unilateral_orbit_bilateral_profile_and_critical_energy
-- name    : MasulloRH.unilateral_orbit_bilateral_profile_and_critical_energy
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T15:57:40.366949+00:00
-- url     : https://prove2.me/theorems/abf04f00-b8e3-4ff8-a3e4-3847b0f0004e
-- title:
--   Uniform renormalized unilateral orbit asymptotic with endpoint drift and critical log-weight energy obstruction
-- statement:
--   Let p>1, q=1/p and H be a continuous complex-valued profile with |H(x)-H(0)|<=C x on [0,p] and |H(x)|<=D/x for x>=1. For 1<=u<=p the unilateral sum over k>=1 of H(p^k q^n u), minus nH(0), converges uniformly to the absolutely convergent bilateral profile B(u). Its error is at most C p q^n/(1-q), B is continuous and B(p)=B(1)-H(0). Wherever |B| is bounded from below on a nondegenerate subinterval, the sum of the renormalized orbit energies over its shrinking annuli diverges, even for the exact critical measure (1+log(t)^2)^2 dt/t.
-- source:
--   Masullo mission, projected semilocal unilateral orbit near a fixed finite place and critical rational global log weight. This statement concerns the orbit profile and its energy rather than a quotient trace identity.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology Interval

theorem MasulloRH.unilateral_orbit_bilateral_profile_and_critical_energy (H : ℝ → ℂ) (cont : Continuous H) (p C D : ℝ) (hp : 1 < p)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hs : ∀ x ∈ Icc 0 p, ‖H x-H 0‖ ≤ C*x) (hl : ∀ x ≥ 1, ‖H x‖ ≤ D/x) :
    let q := p⁻¹
    let U := fun n : ℕ => fun u : ℝ => ∑' k : ℕ, H (p^(k+1)*q^n*u)
    let B := fun u : ℝ => (∑' k : ℕ, H (p^(k+1)*u)) + ∑' k : ℕ, (H (q^k*u)-H 0)
    (∀ u ∈ Icc 1 p, Summable (fun k : ℕ => ‖H (p^(k+1)*u)‖) ∧
      Summable (fun k : ℕ => ‖H (q^k*u)-H 0‖)) ∧ ContinuousOn B (Icc 1 p) ∧
    B p = B 1 - H 0 ∧
    (∀ n : ℕ, ∀ u ∈ Icc 1 p, ‖U n u - (n:ℂ)*H 0 - B u‖ ≤ C*p*q^n/(1-q)) ∧
    TendstoUniformlyOn (fun n : ℕ => fun u => U n u - (n:ℂ)*H 0) B atTop (Icc 1 p) ∧
    ∀ a b η : ℝ, 1 ≤ a → a < b → b ≤ p → 0 < η → (∀ u ∈ Icc a b, η ≤ ‖B u‖) →
      ¬ Summable (fun n : ℕ => ∫ u in a..b, (1+(Real.log (q^n*u))^2)^2 *
        ‖U n u-(n:ℂ)*H 0‖^2 / u) := by sorry
