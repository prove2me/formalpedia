-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_actual_product_grid_pathwise_limit
-- name    : Kyprianou.Ch04.kw47_actual_product_grid_pathwise_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T21:48:43.73153+00:00
-- url     : https://prove2.me/theorems/1d562efb-dd9b-5c44-b186-ccdbf8a61ee2
-- title:
--   Pathwise limit of the Esscher product grid for the actual Kella–Whitt process
-- statement:
--   For every sample path and any monotone vanishing mesh partition of a finite interval, the left predictable Esscher product sums converge to the signed Kella–Whitt increment. Discrete product summation, the vanishing exponential linearisation error and the two reflected quadrature limits establish this without any Lipschitz assumption on the running maximum.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7(i), integration by parts.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_actual_exp_grid_linearization_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_time_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_record_quadrature
import Theorems.Thm_Kyprianou_Ch04_kw47_discrete_product_summation
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual Esscher product grids converge pathwise to the signed
increment of the Kella--Whitt process, on any vanishing-mesh grid. -/

theorem Kyprianou.Ch04.kw47_actual_product_grid_pathwise_limit
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
      H (u n i) * (E (u n (i+1))-E (u n i))) atTop
      (nhds ((Z b-Z a) - L.ψ alpha * (J b-J a) +
        alpha * (runningSup L b w-runningSup L a w))) := by sorry
