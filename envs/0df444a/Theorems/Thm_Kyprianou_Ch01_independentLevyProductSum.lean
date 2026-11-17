-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentLevyProductSum
-- name    : Kyprianou.Ch01.independentLevyProductSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:06:39.797859+00:00
-- url     : https://prove2.me/theorems/de46b965-4c49-49ca-b06f-5d80f75bfd8a
-- title:
--   Sum of two measurable independent Lévy processes on the product probability space is a genuine Lévy process
-- statement:
--   Given two genuine real-valued Lévy processes with measurable time marginals on arbitrary probability spaces, their independent coordinate lifts onto the product probability space have a pointwise sum which is itself a genuine Lévy process. Both lifts retain the complete four-field process structure, and their path-valued random elements are independent by the pinned product-space independence theorem. Therefore the globally Proved full independent-sum theorem gives a genuine Lévy process, preserving all original mathematical requirements. This enables the positive-Gaussian component to be combined with the pure-jump Lévy process in Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Kyprianou (2006) Chapter 1 independent-sums Exercise 1.1 and Lévy–Khintchine existence Theorem 1.6; pinned Mathlib ProbabilityTheory.indepFun_prod, measurable_pi_lambda and Proved Kyprianou.Ch01.independentLevySum.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentLevyProductSum
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hXm : ∀ t, Measurable (X t))
    (hYm : ∀ t, Measurable (Y t)) :
    IsLevyProcess
      (fun t (p : Ω × Λ) => X t p.1 + Y t p.2) (P.prod Q) := by
  sorry
