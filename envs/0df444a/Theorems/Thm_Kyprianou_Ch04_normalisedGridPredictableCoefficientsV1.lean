-- Prove2me | Theorems.Thm_Kyprianou_Ch04_normalisedGridPredictableCoefficientsV1
-- name    : Kyprianou.Ch04.normalisedGridPredictableCoefficientsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:50:38.648478+00:00
-- url     : https://prove2.me/theorems/583200cd-2334-4cfd-9674-1a26000b67a0
-- title:
--   normalisedGridPredictableCoefficientsV1
-- statement:
--   Past-measurable bounded grid coefficients agree with the physical normalised left weights almost surely.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.normalisedGridPredictableCoefficientsV1  {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (Y L : NNReal → Ω → ℝ) (hY : Adapted F Y)
    (hl : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => Y s w) (𝓝[<] t) (𝓝 (L t w)))
    (f : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hBound : ∀ s x : ℝ, 0 ≤ s → |f s x| ≤ K)
    (u : ℕ → NNReal) :
    ∃ H : ℕ → Ω → ℝ, (∀ k, Measurable[F (u k)] (H k)) ∧
      (∀ k w, |H k w| ≤ K) ∧ ∀ᵐ w ∂P, ∀ k,
        H k w = if u k = 0 then 0 else f (u k) (L (u k) w) := by
  sorry
