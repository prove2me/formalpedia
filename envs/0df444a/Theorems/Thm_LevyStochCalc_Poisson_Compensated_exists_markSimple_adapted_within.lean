-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_exists_markSimple_adapted_within
-- name    : LevyStochCalc.Poisson.Compensated.exists_markSimple_adapted_within
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:42:22.594151+00:00
-- url     : https://prove2.me/theorems/ae040959-c625-45ae-9c52-f8dd82eb843a
-- title:
--   exists markSimple adapted within
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.exists_markSimple_adapted_within` is extracted from `LevyStochCalc.Poisson.CompensatedDensityMarkApprox`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark discretisation of the shifted dyadic eval

Approximation of the mark dependence of the adapted dyadic eval by finite mark-simple functions
`∑ₖ cₖ(ω) 𝟙_{Bₖ}(e)` with bounded, adapted coefficients, obtained by running the rectangle
density argument on each time piece over the trimmed product measure. Summing the per-piece
errors gives an `L²(P ⊗ ds ⊗ ν)` approximating sequence of adapted, mark-simple,
piecewise-constant-in-time integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] in

theorem _root_.LevyStochCalc.Poisson.Compensated.exists_markSimple_adapted_within
    {m0 : MeasurableSpace Ω} {P : @Measure Ω m0} [@IsFiniteMeasure Ω m0 P]
    {ν : Measure E} [SigmaFinite ν]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (h : Ω → E → ℝ)
    (h_meas : @Measurable (Ω × E) ℝ (m.prod inferInstance) _ (fun q => h q.1 q.2))
    {C : ℝ} (h_bdd : ∀ ω e, |h ω e| ≤ C)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hsupp : ∀ ω e, e ∉ S → h ω e = 0)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ (K : ℕ) (B : Fin K → Set E) (c : Fin K → Ω → ℝ),
      (∀ k, MeasurableSet (B k)) ∧ (∀ k, B k ⊆ S) ∧
      (∀ k, @Measurable Ω ℝ m _ (c k)) ∧
      (∀ k, ∃ M, ∀ ω, |c k ω| ≤ M) ∧
      ∫⁻ ω, ∫⁻ e, (‖h ω e
          - ∑ k, c k ω * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P ≤ δ := by sorry
