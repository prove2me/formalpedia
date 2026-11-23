-- Prove2me | Theorems.Thm_Kyprianou_Ch02_realLawEqOfAETendstoApproximantsV1
-- name    : Kyprianou.Ch02.realLawEqOfAETendstoApproximantsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:42:07.922802+00:00
-- url     : https://prove2.me/theorems/d64b8281-d73b-4167-9e82-318c02b53d66
-- title:
--   Almost-sure limits of equal-law real approximants have equal pushforward laws
-- statement:
--   For a probability measure, if F_n and G_n are measurable real random variables, share the same law at each n, and converge almost surely respectively to measurable X and Y, then X and Y have the same law. Use MeasureTheory.tendstoInMeasure_of_tendsto_ae, MeasureTheory.TendstoInMeasure.tendstoInDistribution, and uniqueness of probability-measure weak limits. This theorem is general and helps both Kyprianou Ch02 signed marked PRM stationarity and Avram limit-law arguments.
-- source:
--   Mathlib theorem-based measure-theoretic law-limit transfer; Kyprianou (2006) Chapter 2 Eq. (2.3).

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.realLawEqOfAETendstoApproximantsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F G : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hF : ∀ n, Measurable (F n)) (hG : ∀ n, Measurable (G n))
    (hX : Measurable X) (hY : Measurable Y)
    (hLaw : ∀ n, P.map (F n) = P.map (G n))
    (hFlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (X ω)))
    (hGlim : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (𝓝 (Y ω))) :
    P.map X = P.map Y := by sorry
