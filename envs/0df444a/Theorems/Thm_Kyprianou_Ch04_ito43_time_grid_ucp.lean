-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_time_grid_ucp
-- name    : Kyprianou.Ch04.ito43_time_grid_ucp
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T10:49:37.626321+00:00
-- url     : https://prove2.me/theorems/817e3d27-8b78-4961-84b0-576d0974226a
-- title:
--   Uniform-in-probability convergence of stopped time increments to the time derivative integral
-- statement:
--   Uniform-in-probability convergence of stopped time increments to the time derivative integral.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.ito43_time_grid_ucp
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (f : Real × Real -> Real)
    (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ))
 :
    ∀ (T : NNReal) (epsilon : Real), 0 < epsilon →
    Tendsto (fun n : Nat =>
      (P {omega : Omega | ∃ t : NNReal, t ≤ T ∧
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        epsilon ≤ abs ((∫ s in Set.Icc (0 : Real) (t : Real),
          fderiv Real f ((s : Real), X (Real.toNNReal s) omega) (1, 0) ∂volume) - (∑ k ∈ Finset.range n,
          (f ((v (k+1) : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v (k+1)) omega))))}).toReal)
      atTop (nhds 0) := by sorry
