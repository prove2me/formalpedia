-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_markSumProcess_L2_eq
-- name    : LevyStochCalc.Poisson.Compensated.markSumProcess_L2_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:27:05.058177+00:00
-- url     : https://prove2.me/theorems/5cb3ce6d-b295-445a-8ae2-68ff3909eca0
-- title:
--   markSumProcess L2 eq
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.markSumProcess_L2_eq` is extracted from `LevyStochCalc.Poisson.CompensatedDensityMarkSum`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F001

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

theorem _root_.LevyStochCalc.Poisson.Compensated.markSumProcess_L2_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k)) :
    ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, ξ i k ω * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2
        ∂volume ∂ν) ∂P
      = ∑ i : Fin N₀, ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ i k ω * ξ i k' ω ∂P := by sorry
