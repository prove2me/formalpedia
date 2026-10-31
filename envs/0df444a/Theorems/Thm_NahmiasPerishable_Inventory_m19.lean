-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m19
-- name    : NahmiasPerishable.Inventory.m19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:56.503887+00:00
-- url     : https://prove2.me/theorems/963692e1-c60c-43c5-9c88-05cf5bd5a200
-- title:
--   Exponential lifetimes give binomial survivors
-- statement:
--   it follows that the number of units surviving to time t + s is a binomial random variable with parameters n = I(t) and p = e⁻ᶿˢ. It follows that the expected number of units surviving until time t + s is np or I(t)exp{−θs}.
--
--   Differences from the source:
--   - reading: the survivor count is binomial for exponential unit lifetimes → independent exponential lifetimes of the individual units; reason: independence is implicit in the source’s binomial calculation
--   - encoding: conditional on the population surviving at t → joint-event binomial probabilities and the event-integrated mean for every surviving set; reason: this avoids division by a zero-probability conditioning event and covers n=0, s=0 and the empty surviving set
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §2, Exponential lifetimes give binomial survivors (unnumbered), p. 697 (PDF 18), DOI:10.1287/opre.30.4.680; review attribution: Review derivation (no separately attributed original).

import Definitions.Def_NahmiasPerishable_Inventory_AllocationSurvival

open MeasureTheory ProbabilityTheory Set

namespace NahmiasPerishable.Inventory

theorem m19 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (T : Fin n → Ω → ℝ) (theta : ℝ) (htheta : 0 < theta)
    (hT : ∀ i, Measurable (T i)) (hind : iIndepFun T μ)
    (hlaw : ∀ i, μ.map (T i) = expMeasure theta)
    (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (J : Finset (Fin n)) :
    (∀ k : ℕ,
      μ {ω | survivors T t ω = J ∧ (survivors T (t+s) ω).card = k} =
        μ {ω | survivors T t ω = J} *
          ENNReal.ofReal (if k ≤ J.card then
            (J.card.choose k : ℝ) * (Real.exp (-theta*s))^k *
              (1-Real.exp (-theta*s))^(J.card-k) else 0)) ∧
    (∫ ω in {ω | survivors T t ω = J}, ((survivors T (t+s) ω).card : ℝ) ∂μ) =
      (μ {ω | survivors T t ω = J}).toReal * J.card * Real.exp (-theta*s) := by sorry

end NahmiasPerishable.Inventory
