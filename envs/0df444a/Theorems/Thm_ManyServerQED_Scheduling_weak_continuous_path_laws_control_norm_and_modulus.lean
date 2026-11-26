-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_weak_continuous_path_laws_control_norm_and_modulus
-- name    : ManyServerQED.Scheduling.weak_continuous_path_laws_control_norm_and_modulus
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:22:41.023242+00:00
-- url     : https://prove2.me/theorems/3103aaf7-d8f6-597a-aa75-239367c25747
-- title:
--   Weakly converging continuous path laws control norms and moduli
-- statement:
--   Under weak convergence on continuous real-valued paths on the unit interval, the norm tails and the probability of a modulus above a fixed threshold can be made jointly arbitrarily small, eventually along the sequence.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_DurrettProbability_Donsker
open Set Filter Topology MeasureTheory ProbabilityTheory DurrettProbability
open scoped ENNReal NNReal

theorem ManyServerQED.Scheduling.weak_continuous_path_laws_control_norm_and_modulus {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → PathSpace) (Y : Ω' → PathSpace)
    (h : TendstoInDistribution X atTop Y (fun _ => P) P')
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ A > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | A ≤ ‖X n ω‖ ∨ ∃ s t : Set.Icc (0:ℝ) 1,
        dist s t ≤ δ ∧ ε ≤ |X n ω s-X n ω t|} ≤ ENNReal.ofReal η := by sorry
