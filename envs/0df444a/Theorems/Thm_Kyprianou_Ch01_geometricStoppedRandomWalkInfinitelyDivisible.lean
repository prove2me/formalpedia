-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricStoppedRandomWalkInfinitelyDivisible
-- name    : Kyprianou.Ch01.geometricStoppedRandomWalkInfinitelyDivisible
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:18:51.267525+00:00
-- url     : https://prove2.me/theorems/043c211b-f601-4303-8085-f36b5c4550ef
-- title:
--   Exercise 1.2(ii): a random walk stopped at an independent geometric index is infinitely divisible
-- statement:
--   For an arbitrary real-valued random walk with IID jumps and an independent geometric number Γ_p of steps, prove that the law of S_(Γ_p) is infinitely divisible. The whole jump sequence is independent of Γ_p; the concrete law of the stopped sum is the theorem conclusion. This is a strong source-exact formulation of Exercise 1.2(ii). Draft has not been remotely elaborated.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), printed pp. 26–27.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricStoppedRandomWalkInfinitelyDivisible
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
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
    LevyFoundations.isInfinitelyDivisibleLaw
      (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) := by
  sorry
