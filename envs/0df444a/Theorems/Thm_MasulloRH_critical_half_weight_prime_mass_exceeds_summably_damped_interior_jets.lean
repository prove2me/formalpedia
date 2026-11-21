-- Prove2me | Theorems.Thm_MasulloRH_critical_half_weight_prime_mass_exceeds_summably_damped_interior_jets
-- name    : MasulloRH.critical_half_weight_prime_mass_exceeds_summably_damped_interior_jets
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:50:29.73622+00:00
-- url     : https://prove2.me/theorems/d75c0bb0-766e-43dc-904f-96ef73ed6571
-- title:
--   At critical half weight, the translated prime shell exceeds every summably damped interior jet budget
-- statement:
--   Write $X=2^n$. Let $a_j\ge0$, $\delta_j>0$, $k_j\in\mathbf N$ and assume $\sum_j a_j k_j!/\delta_j^{k_j}<\infty$. For every sufficiently large $n$, the actual prime shell satisfies
--   $$\sum_{X<p\le8X}\frac{\log p}{\sqrt p}\ge\sqrt X\left[\frac{\log2}{2\sqrt8}+\sum_j a_j n^{k_j}e^{-\delta_j n}\right].$$
--   For a fixed test with a flat top on $[X,8X]$, the left side is already present in the $k=-1$ local prime-power contributions after inserting the half-twist. In a critical-width translation eigenmode $b_j<1/2$, the cost normalized by $\sqrt X$ has exponential damping $\delta_j=(1/2-b_j)\log2$. The result includes all semisimple modes with summable costs and gives an explicit sufficient condition for mixed polynomial jets. It does not assert that Masullo's full spectral decomposition satisfies this summability condition.
-- source:
--   Masullo, The Music of the Primes, frozen 20 November 2026, (10.4.3.39–45), (11.3.2.1–5); endpoint of the global quotient-diagonal comparison 253e2820-f698-4f31-8af1-176210b3731c. Mathlib Chebyshev.theta_ge and theta_le_log4_mul_x, dominated convergence for series.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Real Filter Finset Asymptotics
open scoped Topology

theorem MasulloRH.critical_half_weight_prime_mass_exceeds_summably_damped_interior_jets (a gap : ℕ → ℝ) (k : ℕ → ℕ) (ha : ∀ j, 0 ≤ a j) (hgap : ∀ j, 0 < gap j)
    (hsum : Summable (fun j => a j * ((k j).factorial:ℝ) / (gap j)^(k j))) :
    ∀ᶠ n : ℕ in atTop,
      let X := (2:ℕ)^n
      let S := Nat.primesLE (8*X) \ Nat.primesLE X
      (Real.log 2 / (2*Real.sqrt 8) +
        ∑' j, a j * ((n:ℝ)^(k j) * Real.exp (-(gap j)*(n:ℝ)))) * Real.sqrt (X:ℝ) ≤
        ∑ p ∈ S, Real.log p / Real.sqrt p := by sorry
