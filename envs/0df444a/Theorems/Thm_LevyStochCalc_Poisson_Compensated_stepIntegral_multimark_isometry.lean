-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_stepIntegral_multimark_isometry
-- name    : LevyStochCalc.Poisson.Compensated.stepIntegral_multimark_isometry
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T23:42:49.017033+00:00
-- url     : https://prove2.me/theorems/ad53e179-d969-45ec-89d7-7abc4b1af0e1
-- title:
--   stepIntegral multimark isometry
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.stepIntegral_multimark_isometry` is extracted from `LevyStochCalc.Poisson.CompensatedDensityBoxIsometry`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F001

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

theorem _root_.LevyStochCalc.Poisson.Compensated.stepIntegral_multimark_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {N₀ K : ℕ} {T : ℝ} (hT : 0 < T)
    (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpleT : p (Fin.last N₀) ≤ T) (hpmono : StrictMono p)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (hBdisj : Pairwise (fun k k' => Disjoint (B k) (B k')))
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k))
    (h_adapt : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ i k)) :
    ∫ ω, (∑ k : Fin K, ∑ i : Fin N₀,
        ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2 ∂P
      = ∑ k : Fin K, ∑ i : Fin N₀,
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k)).toReal * ∫ ω, (ξ i k ω) ^ 2 ∂P := by sorry
