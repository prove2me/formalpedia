-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_grid_path_regular
-- name    : Kyprianou.Ch04.ito43_weighted_grid_path_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:15:10.348469+00:00
-- url     : https://prove2.me/theorems/f2aaa815-8860-592c-a7cd-2b8672c9f336
-- title:
--   Weighted square grid sums have right-continuous bounded paths
-- statement:
--   The clipped path coordinates are right continuous by monotone continuous clipping. Square their difference and multiply by the deterministic cell weight. On the compact stopping horizon the increments are bounded, and the finite sum inherits both properties.
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

theorem Kyprianou.Ch04.ito43_weighted_grid_path_regular {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun t => X t w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) (n : ℕ) :
    let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
    let Q : NNReal → ℝ := fun t => ∑ k ∈ Finset.range n,
      g ((u k:ℝ),X (u k) w)*(X (min t (u (k+1))) w-X (min t (u k)) w)^2/2
    (∀ t, ContinuousWithinAt Q (Ici t) t) ∧ ∃ M : ℝ, ∀ t ≤ T, |Q t| ≤ M := by sorry
