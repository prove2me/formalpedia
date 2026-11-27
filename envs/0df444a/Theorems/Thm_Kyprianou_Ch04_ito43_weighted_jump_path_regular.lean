-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_jump_path_regular
-- name    : Kyprianou.Ch04.ito43_weighted_jump_path_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:15:10.761366+00:00
-- url     : https://prove2.me/theorems/7bdef855-9112-4f19-a583-ef44c9f47983
-- title:
--   Weighted cumulative actual jump integral is right continuous and compact bounded
-- statement:
--   Use the general atomic kernel series identity and locally absolute summability from the compact weight bound and squared jump energy. Apply Chapter 2's proved cumulative jump-series right continuity theorem; the energy bound gives compact boundedness.
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

theorem Kyprianou.Ch04.ito43_weighted_jump_path_regular {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun t => X t w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal)
    (hs : ∀ H : NNReal, Summable (fun s : Ioc (0:NNReal) H => (X s w-L s w)^2)) :
    let J : NNReal → ℝ := fun t =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        g (z.1,L z.1.toNNReal w)*z.2^2/2 ∂(pathJumpMeasure X L w)
    (∀ t, ContinuousWithinAt J (Ici t) t) ∧ ∃ M : ℝ, ∀ t ≤ T, |J t| ≤ M := by sorry
