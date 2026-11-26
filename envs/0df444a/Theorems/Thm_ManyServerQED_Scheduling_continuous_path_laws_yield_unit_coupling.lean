-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_continuous_path_laws_yield_unit_coupling
-- name    : ManyServerQED.Scheduling.continuous_path_laws_yield_unit_coupling
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T21:05:32.332253+00:00
-- url     : https://prove2.me/theorems/9c18bf30-0e92-5c7b-aeaa-8d4f50213ff5
-- title:
--   Skorohod coupling of convergent continuous path laws
-- statement:
--   Let the laws of random continuous paths on $[0,1]$ converge weakly in the uniform topology. Then their coordinate-evaluation process laws admit the unit-interval Skorohod coupling used for càdlàg paths.
-- source:
--   Supporting lemma for the proof of Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_DurrettProbability_Donsker
import Definitions.Def_Reiman84_QueueLength_Paths
open MeasureTheory Filter Topology DurrettProbability Reiman84.QueueLength

theorem ManyServerQED.Scheduling.continuous_path_laws_yield_unit_coupling (μn : ℕ → ProbabilityMeasure PathSpace) (μ : ProbabilityMeasure PathSpace)
    (hμ : Tendsto μn atTop (𝓝 μ)) :
    WeakConvD (fun n => (μn n : Measure PathSpace))
      (fun _ f t => fun _ : Fin 1 => f (Set.projIcc 0 1 zero_le_one t))
      (μ : Measure PathSpace)
      (fun f t => fun _ : Fin 1 => f (Set.projIcc 0 1 zero_le_one t)) := by sorry
