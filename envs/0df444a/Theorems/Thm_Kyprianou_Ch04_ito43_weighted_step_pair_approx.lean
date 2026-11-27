-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_step_pair_approx
-- name    : Kyprianou.Ch04.ito43_weighted_step_pair_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:13:58.275224+00:00
-- url     : https://prove2.me/theorems/fed0efc4-3994-5550-bb8e-557d1a607b2e
-- title:
--   Finite right-step and left-step pair approximates continuous path weight
-- statement:
--   Apply the finite small-oscillation partition of a cadlag weight on the larger compact interval. Represent the step function by successive increments of its values, including the initial value at zero. The left limit uses the strict inequality at every breakpoint.
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

theorem Kyprianou.Ch04.ito43_weighted_step_pair_approx  {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → ℝ) (w : Omega)
    (hc : IsCadlag (fun t => X t w))
    (hl : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t w)))
    (σ : ℝ) (hσ : 0 ≤ σ)
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)))
    (T : NNReal)
    (hs : Summable (fun s : Set.Ioc (0:NNReal) (T+1) => (X s w-Xleft s w)^2))
 :
    let W : ℕ → (ℕ → NNReal) → (ℕ → ℝ) → NNReal → ℝ :=
      fun m b c s => ∑ i ∈ Finset.range m, c i * (if b i ≤ s then (1:ℝ) else 0)
    let L : ℕ → (ℕ → NNReal) → (ℕ → ℝ) → NNReal → ℝ :=
      fun m b c s => ∑ i ∈ Finset.range m, c i * (if b i < s then (1:ℝ) else 0)
    ∀ δ : ℝ, 0 < δ → ∃ (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ),
(∀ s ≤ T, |g ((s:ℝ),X s w)-W m b c s| ≤ δ) ∧
      (∀ s : NNReal, 0 < s → s ≤ T → |g ((s:ℝ),Xleft s w)-L m b c s| ≤ δ) := by sorry
