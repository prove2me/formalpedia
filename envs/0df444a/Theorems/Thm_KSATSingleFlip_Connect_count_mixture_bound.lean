-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_count_mixture_bound
-- name    : KSATSingleFlip.Connect.count_mixture_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:47:34.100735+00:00
-- url     : https://prove2.me/theorems/31a5c281-7faf-4ae6-a256-4a1a9e0833ed
-- title:
--   Count-mixture bound with an exceptional set
-- statement:
--   Partition an event by an integer-valued count. If on every count fiber its part outside an exceptional event has measure at most p times the fiber measure, then its total probability is at most p plus the probability of the exceptional event. This is the conditioning step for the Poisson-count case of Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem KSATSingleFlip.Connect.count_mixture_bound {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N) (E B : Set Ω) (hE : MeasurableSet E) (hB : MeasurableSet B)
    (p : ℝ≥0∞)
    (hfiber : ∀ j : ℕ, μ ((E \ B) ∩ N ⁻¹' {j}) ≤ μ (N ⁻¹' {j})*p) :
    μ E ≤ p + μ B := by sorry
