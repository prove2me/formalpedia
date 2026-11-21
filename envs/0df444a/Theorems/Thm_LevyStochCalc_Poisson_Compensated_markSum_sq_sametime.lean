-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_markSum_sq_sametime
-- name    : LevyStochCalc.Poisson.Compensated.markSum_sq_sametime
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T07:36:47.877552+00:00
-- url     : https://prove2.me/theorems/2ebaeb4d-b9c0-4e5d-ada9-eeb01ef66678
-- title:
--   markSum sq sametime
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.markSum_sq_sametime` is extracted from `LevyStochCalc.Poisson.CompensatedDensityMarkSum`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Poisson.Compensated.markSum_sq_sametime
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {K : ℕ}
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin K → Ω → ℝ) (hξb : ∀ k, ∃ M, ∀ ω, |ξ k ω| ≤ M) (hξm : ∀ k, Measurable (ξ k))
    (hadapt : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) (ξ k)) :
    ∫ ω, (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω) ^ 2 ∂P
      = ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ k ω * ξ k' ω ∂P := by sorry
