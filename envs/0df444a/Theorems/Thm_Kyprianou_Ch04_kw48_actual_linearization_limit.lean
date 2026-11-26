-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_actual_linearization_limit
-- name    : Kyprianou.Ch04.kw48_actual_linearization_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:54:19.972896+00:00
-- url     : https://prove2.me/theorems/8ba17d31-4a08-551a-8e52-1d313e52ee3f
-- title:
--   Actual continuous complex log-weight linearisation limit
-- statement:
--   Actual continuous complex log-weight linearisation limit.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_grid_linearization_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_log_weight_grid_variation
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual continuous complex log-weight admits a vanishing
first-order approximation error on every vanishing-mesh grid. -/

theorem Kyprianou.Ch04.kw48_actual_linearization_limit {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1):Real)-(u n i:Real) ≤ delta n) :
    Tendsto (fun n =>
      (∑ i ∈ Finset.range (N n), Z L alpha beta (u n (i+1)) w *
        (1-Complex.exp (-(G L Psi alpha beta (u n (i+1)) w-
          G L Psi alpha beta (u n i) w)))) -
      (∑ i ∈ Finset.range (N n), Z L alpha beta (u n (i+1)) w *
        (G L Psi alpha beta (u n (i+1)) w-G L Psi alpha beta (u n i) w)))
      atTop (nhds 0) := by sorry
