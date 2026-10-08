-- Prove2me | Theorems.Thm_OAI_InvariantIsing_limiting_pressure_of_extreme_limits_unconditional
-- name    : OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:47.820808+00:00
-- url     : https://prove2.me/theorems/f4ca8da1-f18b-451c-ac33-ee3afcd272be
-- statement:
--   The theorem states that, for a probability space (Ω,P) carrying measurable random orthogonal matrices U_N in O(N) whose pushforward laws P∘U_N⁻¹ are right-invariant under multiplication (Haar-distributed), and deterministic eigenvalue vectors eig_N in ℝ^N, suppose ν is a probability measure on ℝ with compact support contained in [a,b] and with both endpoints a and b belonging to the support. Assume the smallest entries of eig_{k+1} converge to a, the largest entries converge to b, and the empirical spectral laws of eig_{k+1} (the uniform averages of point masses at the entries) converge weakly to ν as k→∞. Define the rotated Ising pressure at zero external field as (1/N) times the logarithm of the average over spin configurations σ∈{±1}^N of exp((1/2)∑_i eig_i (U⁻¹σ)_i²), where U⁻¹ acts on the spin vector. Then the expectation of this pressure, with U=U_N(ω) inverted, converges as N→∞ to the real value of the variational functional evaluated at the function measureR(ν,b), built from ν and the right endpoint b through the inverse of the resolvent ∫1/(b−y)dν(y) (equal to the mean of ν at nonpositive argument). Moreover, P-almost surely in ω, the random pressure itself converges to the same limit. The variational functional is defined as an infimum over monotone overlap paths of an entropy functional plus a spectral functional. The theorem is admitted in the source, not proved there.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InvariantIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InvariantIsing.lean; bytes 12402..13601
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

theorem limiting_pressure_of_extreme_limits_unconditional :
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (_hU : ∀ N, Measurable (U N))
    (_hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hcompact : IsCompact (ν : Measure ℝ).support)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hmin : Tendsto (fun k => spectralMinimum (eig (k+1))) atTop (𝓝 a))
    (_hmax : Tendsto (fun k => spectralMaximum (eig (k+1))) atTop (𝓝 b))
    (_hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)),
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (fun _ => 0))
      atTop (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  sorry

end InvariantIsing
end
end OAI
