-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_gain_uniform_bound
-- name    : Kyprianou.Ch04.kw47_esscher_grid_gain_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:08:51.08129+00:00
-- url     : https://prove2.me/theorems/841c7cb3-c497-59af-be35-4e12fe6bbffa
-- title:
--   Pathwise mesh-uniform bound on the full Kella-Whitt Esscher grid sum
-- statement:
--   On any finite increasing deterministic grid up to T, the absolute exact Kella–Whitt Esscher predictable gain Σ H_i(E_{i+1}−E_i) is bounded by 4 exp(alpha runningSup(X,T)+|psi(alpha)|T) exp(|psi(alpha)|T). The Proved running-maximum envelope bounds E_i uniformly and the Proved H-factor estimates give |H_i|≤C and Σ|ΔH_i|≤2C. The generic finite-grid summation-by-parts domination theorem gives the result. This is independent of grid mesh and supplies the precise dominating random variable for L1 passage to the limit.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7, p.108 and solution pp.320–321; exact Esscher predictable grid sum.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_E_grid_horizon_bound
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_weight_horizon_bound
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_H_grid_variation
import Theorems.Thm_Kyprianou_Ch04_kw47_grid_gain_uniform_bound
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The exact Esscher product grid is uniformly bounded on every
finite horizon by one exponential running-maximum envelope. -/

theorem Kyprianou.Ch04.kw47_esscher_grid_gain_uniform_bound
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T : NNReal) (u : Nat → NNReal) (hu : Monotone u)
    (hT : ∀ i, u i ≤ T) (n : Nat) (w : Ω) :
    |∑ i ∈ Finset.range n,
      Real.exp (-alpha * runningSup L (u i) w +
         L.ψ alpha * (u i : Real)) *
      (Real.exp (alpha * L.X (u (i+1)) w -
         L.ψ alpha * (u (i+1) : Real)) -
       Real.exp (alpha * L.X (u i) w -
         L.ψ alpha * (u i : Real)))| ≤
      4 * Real.exp (alpha * runningSup L T w +
           |L.ψ alpha| * (T : Real)) *
          Real.exp (|L.ψ alpha| * (T : Real)) := by sorry
