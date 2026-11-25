-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_actual_grid_correction
-- name    : Kyprianou.Ch04.kw47_actual_grid_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:52:08.766169+00:00
-- url     : https://prove2.me/theorems/9b6dfa4e-5041-43c2-b91f-369d74de2bbb
-- title:
--   Right-point exponential correction converges to time and running-record increments
-- statement:
--   The right-point product correction converges by the first-order exponential expansion, the time quadrature limit and the running-record quadrature limit.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_exp_grid_linearization_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_time_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_record_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw47_discrete_product_summation
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false


/-- The right-point exponential correction converges to the time and record terms. -/

theorem Kyprianou.Ch04.kw47_actual_grid_correction
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
    let E : NNReal → Real := fun r =>
      Real.exp (alpha * L.X r w - L.ψ alpha * (r:Real))
    let H : NNReal → Real := fun r =>
      Real.exp (-alpha * runningSup L r w + L.ψ alpha * (r:Real))
    let Z : NNReal → Real := fun r =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    let J : NNReal → Real := fun t =>
      ∫ x in Icc (0:Real) (t:Real), Z x.toNNReal ∂volume
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      E (u n (i+1)) * (H (u n (i+1))-H (u n i))) atTop
      (nhds (L.ψ alpha * (J b-J a)-alpha*(runningSup L b w-runningSup L a w))) := by sorry
