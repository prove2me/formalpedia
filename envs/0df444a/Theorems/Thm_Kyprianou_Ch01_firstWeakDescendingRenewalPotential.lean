-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstWeakDescendingRenewalPotential
-- name    : Kyprianou.Ch01.firstWeakDescendingRenewalPotential
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:22:16.851391+00:00
-- url     : https://prove2.me/theorems/d3c1de7a-33c5-447b-8240-9933786c7750
-- title:
--   Exercise 1.8(ii): weak descending ladder law from positive-path potential
-- statement:
--   Exercise 1.8(ii), printed pp. 29–30: the first weak descending passage distribution of a random walk (T_0^-=inf{n>0:S_n≤0}) is the convolution of its step distribution μ with the potential measure of strictly positive surviving paths. That potential is Σ_{n≥0}P(S_n∈dy, S_1>0,...,S_n>0) and by the Exercise 1.8(i) reversal lemma equals the strict ascending ladder renewal measure V. The expression is quantified for all measurable B contained in (−∞,0]. The conclusion is a genuine weak-descending renewal identity, with no assumption of it.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.8(ii), printed pp. 29–30.

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.firstWeakDescendingRenewalPotential
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (hindep : iIndepFun increment P)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hLaw : ∀ n : ℕ, HasLaw (increment n) mu P) :
    let S : ℕ → Ω → ℝ :=
      fun n ω => ∑ i ∈ Finset.range n, increment i ω
    ∀ B : Set ℝ, MeasurableSet B →
      B ⊆ Set.Iic (0 : ℝ) →
        P {ω | ∃ n : ℕ, 1 ≤ n ∧ S n ω ∈ B ∧
          ∀ j : ℕ, 1 ≤ j → j < n → 0 < S j ω} =
          ∑' n : ℕ,
            ∫⁻ y : ℝ, mu
              ((fun z : ℝ => y + z) ⁻¹' B) ∂
              (Measure.map (S n)
                (P.restrict {ω | ∀ j : ℕ,
                    1 ≤ j → j ≤ n → 0 < S j ω})) := by
  sorry
