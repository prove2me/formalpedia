-- Prove2me | Theorems.Thm_ItoLemma_clock_coordinate_eq_time_ae
-- name    : ItoLemma.clock_coordinate_eq_time_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:44:09.800928+00:00
-- url     : https://prove2.me/theorems/277bc70c-7001-4d57-a8bc-d4f6b31a8eef
-- title:
--   Clock Coordinate of an Augmented Itô Process
-- statement:
--   Let X be a continuous adapted two-coordinate vector Itô version driven by a finite-dimensional Brownian motion. Suppose its clock coordinate starts at zero, has deterministic drift identically one and has diffusion coefficient identically zero under each Brownian driver. Then, for every fixed nonnegative time t, the clock coordinate Xₜ⁽⁰⁾ equals t almost surely. This isolates the clock-process identity necessary to transfer the existing time-independent vector Itô theorem into a time-dependent scalar formula. It is a fixed-time almost-sure assertion, not a claimed indistinguishability result.
-- source:
--   Auxiliary stochastic-process lemma for the clock-augmentation proof of Itô's lemma. Based on the integral representation in the accepted Prove2Me definition of IsVectorItoVersion and the accepted zero Itô-integral theorem UUID 25be55e0-49ef-4e33-bce3-85281b56b4d4. Mathematical context: https://en.wikipedia.org/wiki/It%C3%B4%27s_lemma (accessed 26 October 2026).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoVersionExists

open MeasureTheory ProbabilityTheory
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal

universe u

/-- A vector Itô version whose initial clock is zero and whose clock
coefficients are deterministic drift one and diffusion zero has its first
coordinate equal to the real time parameter almost surely. -/

theorem ItoLemma.clock_coordinate_eq_time_ae
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    (H : Fin 2 → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin 2) (k : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (X₀ : Ω → Fin 2 → ℝ)
    (bdrift : Fin 2 → Ω → ℝ → ℝ)
    (X : ℝ → Ω → Fin 2 → ℝ)
    (hX : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hclock₀ : ∀ ω, X₀ ω 0 = 0)
    (hclockDrift : ∀ ω s, bdrift 0 ω s = 1)
    (hclockDiff : ∀ k ω s, H 0 k ω s = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    (fun ω => X t ω 0) =ᵐ[P] (fun _ => t) := by sorry
