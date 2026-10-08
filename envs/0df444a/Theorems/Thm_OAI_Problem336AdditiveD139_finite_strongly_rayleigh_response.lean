-- Prove2me | Theorems.Thm_OAI_Problem336AdditiveD139_finite_strongly_rayleigh_response
-- name    : OAI.Problem336AdditiveD139.finite_strongly_rayleigh_response
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:08.324789+00:00
-- url     : https://prove2.me/theorems/05a42776-8529-4594-8196-fcb2db7bc1ac
-- statement:
--   The theorem states that, for every nonempty finite index type F and every probability measure μ on {0,1}-valued configurations x : F → Bool whose generating polynomial Σₓ μ({x}) ∏_{i: xᵢ=true} zᵢ is nonzero whenever every complex variable zᵢ has strictly positive imaginary part (the strongly Rayleigh property), three conclusions hold for the exponentially tilted law, whose weight on x is proportional to exp(Σⱼ hⱼ·1[xⱼ=true])μ({x}) for a real field h : F → ℝ. Write m_h(i) for the tilted probability that coordinate i is true and Cov_h(i,j) for the tilted covariance of the indicators of i and j. First, for all i, j and h, the derivative at r = 0 of r ↦ m_{h+r e_j}(i), where r is added only to the j-th coordinate of h, exists and equals Cov_h(i,j). Second, for every i and h, the sum over all j of |Cov_h(i,j)| is at most 2·m_h(i)(1 − m_h(i)), which in turn is at most 1/2. Third, for every i, any two fields h and h' with |hⱼ − h'ⱼ| ≤ D for all j, where D ≥ 0, satisfy |m_h(i) − m_{h'}(i)| ≤ D/2. The proof is admitted rather than supplied.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StronglyRayleighDPP.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StronglyRayleighDPP.lean; bytes 4970..5715
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_StronglyRayleighDPP

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12

universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139

theorem finite_strongly_rayleigh_response :
    ∀ (F : Type u_1) [Fintype F] [Nonempty F] (μ : ProbabilityMeasure (F → Bool)),
      StronglyRayleighFinite μ →
        (∀ (i j : F) (h : F → ℝ),
          HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
            (tiltCovariance μ h i j) 0) ∧
        (∀ (i : F) (h : F → ℝ),
          (∑ j : F, |tiltCovariance μ h i j|) ≤
              2 * tiltMean μ h i * (1 - tiltMean μ h i) ∧
            2 * tiltMean μ h i * (1 - tiltMean μ h i) ≤ (1 : ℝ) / 2) ∧
        (∀ (i : F) (h h' : F → ℝ) (D : ℝ),
          0 ≤ D → (∀ j : F, |h j - h' j| ≤ D) →
            |tiltMean μ h i - tiltMean μ h' i| ≤ D / 2) := by
  sorry

end Problem336AdditiveD139
end
end OAI
