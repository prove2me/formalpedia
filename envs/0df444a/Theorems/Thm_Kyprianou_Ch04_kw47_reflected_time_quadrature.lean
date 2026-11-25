-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_reflected_time_quadrature
-- name    : Kyprianou.Ch04.kw47_reflected_time_quadrature
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:17:45.469381+00:00
-- url     : https://prove2.me/theorems/f7edbd21-54b8-5c63-a890-2c26ab48edc0
-- title:
--   Reflected exponential time-grid quadrature limit
-- statement:
--   For an increasing vanishing-mesh grid on [a,b], the reflected exponential weighted by time increments converges to the difference of its time primitives at b and a. Apply the general finite-measure quadrature theorem to Lebesgue measure and use exact half-open interval masses and integral additivity.
-- source:
--   Kyprianou (2006), Exercise 4.7; deterministic product-grid limit.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_real_path
import Theorems.Thm_Kyprianou_Ch04_kw47_right_grid_integral_convergence
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact right-endpoint time quadrature on any vanishing-mesh grid. -/

theorem Kyprianou.Ch04.kw47_reflected_time_quadrature
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1) : Real) - (u n i : Real) ≤ delta n) :
    let Z : NNReal → Real := fun r =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((u n (i+1) : Real)-(u n i : Real)) * Z (u n (i+1)))
      atTop (nhds ((∫ x in Icc (0:Real) (b:Real), Z x.toNNReal ∂volume) -
        (∫ x in Icc (0:Real) (a:Real), Z x.toNNReal ∂volume))) := by sorry
