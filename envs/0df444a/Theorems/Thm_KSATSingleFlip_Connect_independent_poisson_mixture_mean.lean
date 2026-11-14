-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_independent_poisson_mixture_mean
-- name    : KSATSingleFlip.Connect.independent_poisson_mixture_mean
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:56:08.245193+00:00
-- url     : https://prove2.me/theorems/8186422e-4a34-4766-8447-c8dcff5f6df9
-- title:
--   Mean of an observable selected by an independent Poisson count
-- statement:
--   Let N have a Poisson law and let X_j be an integrable family of real observables, each independent of N. Whenever the selected variable X_N and the fixed-count mean sequence are integrable, E[X_N] equals the Poisson expectation of the fixed-count means E[X_j]. The theorem supplies the mixture-mean identification in Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

theorem KSATSingleFlip.Connect.independent_poisson_mixture_mean {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N) (r : ℝ≥0) (hNlaw : Measure.map N P = poissonMeasure r)
    (X : ℕ → Ω → ℝ) (hX : ∀ j, Measurable (X j))
    (hind : ∀ j, IndepFun N (X j) P)
    (hYint : Integrable (fun ω => X (N ω) ω) P)
    (hgint : Integrable (fun j => ∫ ω, X j ω ∂P) (poissonMeasure r)) :
    (∫ ω, X (N ω) ω ∂P) = ∫ j, (∫ ω, X j ω ∂P) ∂(poissonMeasure r) := by sorry
