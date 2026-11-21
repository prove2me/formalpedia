-- Prove2me | Theorems.Thm_MasulloRH_double_angular_orbit_mass_and_prime_shell_majorant_escape
-- name    : MasulloRH.double_angular_orbit_mass_and_prime_shell_majorant_escape
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:08:12.837699+00:00
-- url     : https://prove2.me/theorems/db985081-fca8-4440-bfd1-276f6e60b4e6
-- title:
--   Double Haar integration gives unit orbit mass and forces unbounded majorants at prime half weight
-- statement:
--   Let a countable orbit group $D$ and angular group $K$ carry a nonnegative jointly normalized indentation $w_n(r,h)$ at each cutoff $n$, integrated using counting measure and left Haar measure. Put $b_n(r)=\int_Kw_n(r,h)\,dh$. With both copies of the angular variable integrated, the overlap at $\xi$ is $C_n(\xi)=\sum_r b_n(r)b_n(r\xi)$, and $\sum_\xi C_n(\xi)=1$. Allow overlap between shell masks $m_n(p,\xi)\ge0$ provided their sum over primes is at most one for each $n,\xi$. If complex prime coefficients satisfy $|A_n(p)|\le M_n\sum_\xi m_n(p,\xi)C_n(\xi)$ and $|A_n(p)|\to c p^{-a}$ at each prime for a fixed $c>0$ and $a\le1$, then $M_n\to+\infty$. In particular this obstruction applies at $a=1/2$, for arbitrary correlated rational and angular weights and for disjoint divisor shells as well as individual prime lifts. It is a necessary condition for a uniform domination of this form, before one can identify any such coefficients with a nuclear trace.
-- source:
--   Masullo, The Music of the Primes, 20 November 2026, (A.2.3.14), (11.3.2.1)–(11.3.2.2), rational norm-fiber coordinates and two Haar integrations. Builds on mission replies 14fd6a10-f6f1-4ccc-8086-e0646856a024 and 9c2d8069-ca31-40d9-ab04-6fc7b8ecb287. Uses Mathlib’s divergence of the sum of prime reciprocal powers.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Real

open MeasureTheory Filter Finset
open scoped ENNReal Topology

theorem MasulloRH.double_angular_orbit_mass_and_prime_shell_majorant_escape {D K : Type*} [Group D] [Countable D] [Group K] [MeasurableSpace K]
    [MeasurableMul₂ K] (μ : Measure K) [SFinite μ] [μ.IsMulLeftInvariant]
    (w : ℕ → D → K → ℝ≥0∞) (hw : ∀ n r, Measurable (w n r))
    (hprob : ∀ n, ∑' r : D, ∫⁻ h : K, w n r h ∂μ = 1) :
    let b := fun n (r : D) => ∫⁻ h : K, w n r h ∂μ
    let C := fun n (ξ : D) =>
      ∫⁻ g : K, ∑' r : D, ∫⁻ h : K, w n r h * w n (r*ξ) (h*g) ∂μ ∂μ
    (∀ n ξ, C n ξ = ∑' r : D, b n r * b n (r*ξ)) ∧ (∀ n, ∑' ξ : D, C n ξ = 1) ∧
      ∀ (mask : ℕ → Nat.Primes → D → ℝ≥0∞), (∀ n ξ, ∑' p : Nat.Primes, mask n p ξ ≤ 1) →
      ∀ (coeff : ℕ → Nat.Primes → ℂ) (M : ℕ → ℝ), (∀ n, 0 ≤ M n) →
        (∀ n p, ENNReal.ofReal ‖coeff n p‖ ≤ ENNReal.ofReal (M n) * ∑' ξ, mask n p ξ * C n ξ) →
        ∀ a c : ℝ, a ≤ 1 → 0 < c →
          (∀ p : Nat.Primes, Tendsto (fun n => ‖coeff n p‖) atTop (𝓝 (c * (p:ℝ)^(-a)))) →
          Tendsto M atTop atTop := by sorry
