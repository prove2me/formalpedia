-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDuality_cadlagDyadicExtremaLimit
-- name    : Kyprianou.Ch03.supInfDuality_cadlagDyadicExtremaLimit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:03:44.115951+00:00
-- url     : https://prove2.me/theorems/edaddf7a-761e-44be-91f5-91803ae38d58
-- title:
--   Convergence of finite dyadic extrema of a cadlag path
-- statement:
--   For a càdlàg real path, the extrema on the finite dyadic grids of a compact time interval converge to the actual interval extrema. The grids include both endpoints; for each time the dyadic ceiling approaches from the right, where the path is continuous. Compact boundedness of the path gives the extrema inequalities.
-- source:
--   Kyprianou (2006), Lemma 3.5, continuous-time limit of finite-grid reversal.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDuality_cadlagDyadicExtremaLimit
    (f : NNReal → ℝ) (hf : IsCadlag f) (t : NNReal) (ht : 0 < t) :
    Tendsto (fun n : ℕ => sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
      f ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))))))
      atTop (nhds (sSup (f '' Set.Icc 0 t))) ∧
    Tendsto (fun n : ℕ => sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
      f ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))))))
      atTop (nhds (sInf (f '' Set.Icc 0 t))) := by sorry
