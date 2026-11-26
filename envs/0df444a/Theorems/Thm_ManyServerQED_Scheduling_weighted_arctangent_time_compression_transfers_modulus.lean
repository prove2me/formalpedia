-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_weighted_arctangent_time_compression_transfers_modulus
-- name    : ManyServerQED.Scheduling.weighted_arctangent_time_compression_transfers_modulus
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:04:15.735536+00:00
-- url     : https://prove2.me/theorems/ba2ee38b-5490-4841-b417-05de9fec4ed3
-- title:
--   Modulus bound under weighted arctangent time compression
-- statement:
--   An asymptotically small uniform modulus in probability on every compact time interval implies an asymptotically small modulus on the unit interval after the weighted arctangent time compression.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_Reiman84_QueueLength_Paths
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy Reiman84.QueueLength

theorem ManyServerQED.Scheduling.weighted_arctangent_time_compression_transfers_modulus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (h : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    let z (n : ℕ) (ω : Ω) (s : ℝ) := max 0 (1-s) • (fun i => Real.arctan (X n ω (s/(1-s)) i))
    ∀ (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1, |s-t| ≤ δ ∧
        ε ≤ ‖z n ω s-z n ω t‖} ≤ ENNReal.ofReal η := by sorry
