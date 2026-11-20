-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_crossSum_disjointMark_zero
-- name    : LevyStochCalc.Poisson.Compensated.crossSum_disjointMark_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T23:41:54.120972+00:00
-- url     : https://prove2.me/theorems/89b4065f-dc56-4903-b174-ec9e70697e3a
-- title:
--   crossSum disjointMark zero
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.crossSum_disjointMark_zero` is extracted from `LevyStochCalc.Poisson.CompensatedDensityBoxIsometry`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Weighted covariances of compensated boxes

Second moments and cross moments of compensated masses `Ñ((a,b] × A)` weighted by a
past-measurable factor: the weighted second moment, vanishing of the cross terms for disjoint
marks and for time-ordered boxes, and the same-time bilinear covariance in the marks. These
combine into the isometry for a single time interval carrying several marks.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.crossSum_disjointMark_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    (A A' : Fin N₀ → Set E)
    (hAm : ∀ i, MeasurableSet (A i)) (hA'm : ∀ i, MeasurableSet (A' i))
    (hAf : ∀ i, ν (A i) ≠ ⊤) (hA'f : ∀ i, ν (A' i) ≠ ⊤)
    (hdisj : ∀ i, Disjoint (A i) (A' i))
    (ξ ξ' : Fin N₀ → Ω → ℝ)
    (hξb : ∀ i, ∃ M, ∀ ω, |ξ i ω| ≤ M) (hξ'b : ∀ i, ∃ M, ∀ ω, |ξ' i ω| ≤ M)
    (hξm : ∀ i, Measurable (ξ i)) (hξ'm : ∀ i, Measurable (ξ' i))
    (h_adapt : ∀ i, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ i))
    (h_adapt' : ∀ i, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ' i)) :
    ∫ ω, (∑ i : Fin N₀, ξ i ω
            * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
        * (∑ j : Fin N₀, ξ' j ω
            * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω) ∂P = 0 := by sorry
