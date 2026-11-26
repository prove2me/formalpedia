-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_functional_coupling_from_fdd_and_interval_modulus
-- name    : ManyServerQED.Scheduling.functional_coupling_from_fdd_and_interval_modulus
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:04:01.668989+00:00
-- url     : https://prove2.me/theorems/9a277e4a-0ef1-56a4-a6a2-9a9de0d2a0a0
-- title:
--   Functional coupling from finite observations and compact-time moduli
-- statement:
--   For finite-dimensional càdlàg processes, finite-dimensional convergence to a continuous process and an asymptotically small uniform modulus on compact time intervals imply the existence of a coupling with almost sure uniform convergence on every compact time interval.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_Reiman84_QueueLength_weakConvD_of_fdd_and_modulus
import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_Reiman84_QueueLength_Paths
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy Reiman84.QueueLength

theorem ManyServerQED.Scheduling.functional_coupling_from_fdd_and_interval_modulus {Ω : Type*} {Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ) (x : Ω' → ℝ → Fin k → ℝ)
    (hX : ∀ n ω i, IsCadlag (fun t => X n ω t i))
    (hXm : ∀ n t, 0 ≤ t → Measurable (fun ω => X n ω t))
    (hx : ∀ ω, ContinuousOn (x ω) (Ici 0))
    (hxm : ∀ t, 0 ≤ t → Measurable (fun ω => x ω t))
    (hF : ∀ (m : ℕ) (τ : Fin m → ℝ), (∀ i, 0 ≤ τ i) →
      TendstoInDistribution (fun n ω i => X n ω (τ i)) atTop
        (fun ω i => x ω (τ i)) (fun _ => P) P')
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    CouplingConverges P P' X x := by sorry
