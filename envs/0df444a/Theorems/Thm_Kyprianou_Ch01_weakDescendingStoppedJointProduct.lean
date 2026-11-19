-- Prove2me | Theorems.Thm_Kyprianou_Ch01_weakDescendingStoppedJointProduct
-- name    : Kyprianou.Ch01.weakDescendingStoppedJointProduct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:09:54.911817+00:00
-- url     : https://prove2.me/theorems/b066818b-ab03-4e51-9253-319e5af112e9
-- title:
--   Past-positive-prefix stopped joint law factorises from its next increment
-- statement:
--   For a random walk with independently and identically distributed measurable increments, restrict the underlying probability measure to the event that every partial sum S(j) for 1<=j<=n stays strictly positive. This event is measurable with respect to the sigma algebra of increments up to n-1. Independence implies the joint pushforward of (S(n), increment(n)) under the stopped/restricted measure equals the product of the restricted law of S(n) and the original common increment law mu. This is the key precise measure-level conditional independence needed for the first weak descending passage convolution.
-- source:
--   Kyprianou (2006), Exercise 1.8(ii), renewal/positive path potential proof, page 304

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Map
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.weakDescendingStoppedJointProduct
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (hindep : iIndepFun increment P)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hLaw : ∀ n : ℕ, HasLaw (increment n) mu P)
    (n : ℕ) :
    let S : ℕ → Ω → ℝ :=
      fun k ω => ∑ i ∈ Finset.range k, increment i ω
    let H : Set Ω :=
      {ω | ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω}
    Measure.map (fun ω => (S n ω, increment n ω))
      (P.restrict H) =
        (Measure.map (S n) (P.restrict H)).prod mu := by
  sorry
