-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricStoppedIIDFiniteLevyIntensity
-- name    : Kyprianou.Ch01.geometricStoppedIIDFiniteLevyIntensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:47:15.622689+00:00
-- url     : https://prove2.me/theorems/0849ea0b-8b6e-4d7f-b72e-d2c1b98f6bca
-- title:
--   Finite nonzero-jump Lévy intensity of a strictly geometrically stopped IID sum
-- statement:
--   For the exact source assumptions of an independent strict geometric stopping count and IID real increments, there exists a finite positive measure Λ supported away from the origin whose compensated Fourier exponent reproduces the characteristic function p/[1−(1−p)φ_jumpLaw(ξ)] at every real frequency. Construct Λ as the countable logarithmic intensity-weighted sum of convolution-power increment laws restricted to ℝ∖{0}. Zero cluster values contribute no Lévy jumps; the construction includes the all-zero increment case with Λ=0.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), finite Lévy-Khintchine intensity for compound-geometric laws.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
open MeasureTheory ProbabilityTheory Complex LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricStoppedIIDFiniteLevyIntensity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ,
      HasLaw (increment n) jumpLaw P)
    (hGeometric : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal (p * (1 - p) ^ k))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P) :
    ∃ Λ : Measure ℝ,
      Λ {0} = 0 ∧
      Λ Set.univ < ⊤ ∧
      ∀ xi : ℝ,
        Integrable (fun x : ℝ =>
          Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) Λ ∧
        Complex.exp
          (∫ x : ℝ,
            (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂Λ) =
          (p : ℂ) /
            (1 - (((1 - p : ℝ) : ℂ) * charFun jumpLaw xi)) := by
  sorry
