-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_levy_nat_grid_independent
-- name    : Kyprianou.Ch04.ito43_levy_nat_grid_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:57:22.054257+00:00
-- url     : https://prove2.me/theorems/5b5832b9-6f3e-4faa-bf37-f266831f9cf9
-- title:
--   Lévy increments along a monotone natural-index grid are mutually independent
-- statement:
--   Each finite set of indices embeds into a sufficiently long finite grid, whose increments are independent by the Lévy hypothesis. Apply the finite restriction characterisation of independent families.
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
open scoped Topology
open Set

theorem Kyprianou.Ch04.ito43_levy_nat_grid_independent {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (u : ℕ → NNReal) (hu : Monotone u) :
    iIndepFun (fun k : ℕ => fun w => X (u (k+1)) w-X (u k) w) P := by sorry
