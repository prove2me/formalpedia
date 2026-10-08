-- Prove2me | Theorems.Thm_OAI_InvariantIsing_gaussianPattern_norm_limits_unconditional
-- name    : OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:47.391989+00:00
-- url     : https://prove2.me/theorems/bc753f9f-c509-450f-8f3b-949bea3c4a53
-- statement:
--   The theorem states that, for every real α>0, every probability space (Ω,P), and every sequence of measurable random vectors Z_N in the Euclidean space indexed by Fin N × Fin m_N, where m_N=⌊αN⌋ and each Z_N has the standard Gaussian law (so Z_N is an N×m_N array of Gaussian entries), there exist real numbers e₊ ≥ 0 and e₋ ≤ 0 with the following properties. First, gaussianPatternLimit(α,β)/β tends to e₊ as β→+∞, and gaussianPatternLimit(α,−β)/β tends to e₋ as β→+∞. Second, the random variables ‖A_{k+1}(Z_{k+1})‖/(k+1) converge to √(2e₊) both in probability and in L¹(P), where A is the gaussianPatternOperator, the continuous linear map v ↦ Zᵀv from the space of functions Fin N → ℝ (with its default norm) to ℝ^{m}, and ‖·‖ is its operator norm. Third, the random variables min over spin configurations σ in Spin(k+1) of ‖Z_{k+1}ᵀσ‖ (the Euclidean norm of gaussianPatternSum), divided by k+1, converge to √(−2e₋) both in probability and in L¹(P).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InvariantIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InvariantIsing.lean; bytes 24112..25408
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_InvariantIsing

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped BigOperators Topology Matrix Classical ENNReal

universe u

namespace InvariantIsing

theorem gaussianPattern_norm_limits_unconditional :
  ∀ (α : ℝ) (_hα : 0 < α)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (_hZ : ∀ N, Measurable (Z N)) (_hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P),
    ∃ eplus eminus : ℝ, 0 ≤ eplus ∧ eminus ≤ 0 ∧
      Tendsto (fun β => gaussianPatternLimit α β/β) atTop (𝓝 eplus) ∧
      Tendsto (fun β => gaussianPatternLimit α (-β)/β) atTop (𝓝 eminus) ∧
      (TendstoInMeasure P (fun k ω => ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1)) atTop
        (fun _ => Real.sqrt (2*eplus)) ∧
       Tendsto (fun k => eLpNorm (fun ω => ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1)-
        Real.sqrt (2*eplus)) 1 P) atTop (𝓝 0)) ∧
      (TendstoInMeasure P (fun k ω =>
        (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1))
        atTop (fun _ => Real.sqrt (-2*eminus)) ∧
       Tendsto (fun k => eLpNorm (fun ω =>
        (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1)-
          Real.sqrt (-2*eminus)) 1 P) atTop (𝓝 0)) := by
  sorry

end InvariantIsing
end
end OAI
