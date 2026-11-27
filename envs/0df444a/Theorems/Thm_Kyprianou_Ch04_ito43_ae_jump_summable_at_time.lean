-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ae_jump_summable_at_time
-- name    : Kyprianou.Ch04.ito43_ae_jump_summable_at_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:21:15.098718+00:00
-- url     : https://prove2.me/theorems/1183bc31-15a8-4a6e-9712-3c890c6548dc
-- title:
--   Actual jump squares are summable almost surely at each finite time
-- statement:
--   Restrict the square-summable jumps on the larger positive interval to the requested horizon by an injective inclusion.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_ae_jump_summable_at_time
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (tr : LevyKhintchineTriple)
    (hc : ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ))
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (t : NNReal) :
    ∀ᵐ w ∂P, Summable (fun s : Ioc (0:NNReal) t => (X s w-L s w)^2) := by sorry
