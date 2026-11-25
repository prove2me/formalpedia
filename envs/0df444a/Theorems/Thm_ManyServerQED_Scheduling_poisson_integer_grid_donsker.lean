-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_poisson_integer_grid_donsker
-- name    : ManyServerQED.Scheduling.poisson_integer_grid_donsker
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T21:05:35.025939+00:00
-- url     : https://prove2.me/theorems/9004a501-a9a6-4b40-a9d7-7c774c0e538d
-- title:
--   Donsker convergence for centered unit-rate Poisson grid increments
-- statement:
--   For a rate-one Poisson process, the rescaled polygonal walk formed from its centered unit-time increments converges to Brownian motion in distribution on $C[0,1]$.
-- source:
--   Supporting lemma for the proof of Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_DurrettProbability_Donsker
import Definitions.Def_ManyServerQED_Scheduling_Model
open MeasureTheory ProbabilityTheory Filter Topology ManyServerQED.Scheduling DurrettProbability
open scoped NNReal ENNReal

theorem ManyServerQED.Scheduling.poisson_integer_grid_donsker {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℝ → ℝ) (hN : IsPoissonProcess P N 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous fun t => B t ω) :
    TendstoInDistribution
      (fun n : ℕ => walkPath (fun j ω => N ω ((j:ℝ)+1) - N ω j - 1) n)
      atTop (brownianPath B) (fun _ => P) P' := by sorry
