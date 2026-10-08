-- Prove2me | Theorems.Thm_OAI_InvariantIsing_limiting_wasserstein_field_pressure_of_extreme_limits_unconditional
-- name    : OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:47.976529+00:00
-- url     : https://prove2.me/theorems/2d7e1498-71b1-4aef-a4b2-dd48f9aec71e
-- statement:
--   The theorem states that, for a probability space (Ω, P) and, for each N, a measurable map U_N from Ω into the real orthogonal group O(N) whose pushforward law under P is invariant under right multiplication (so U_N is Haar-distributed in the sense of right-invariance), suppose eig_N is a vector of N real eigenvalues and ν is a probability measure on ℝ with compact support contained in [a,b], with both endpoints a and b belonging to the support of ν. Assume the smallest entry of eig_{k+1} converges to a and the largest entry converges to b as k→∞, and that the empirical spectral laws of eig_{k+1} (uniform weight 1/(k+1) on each entry) converge weakly to ν. Let field_N be a vector of N real external-field entries and let ξ be a probability measure on ℝ with integrable identity function, such that the Wasserstein-one distance between the empirical law of field_{k+1} and ξ, defined as the infimum of the expected |x−y| over couplings, tends to 0. The conclusion has two parts. First, the expectation over P of the rotated Ising pressure tends, as N→∞, to the magnetic field functional of ν, b and ξ. Second, almost surely in ω, that same pressure converges to this limit. Here the rotated pressure is N⁻¹ times the log of the average over spin configurations σ∈{±1}^N of exp(H), where H = (1/2)Σ eig_N(i)·(U_N(ω)⁻¹σ)_i² + Σ field_N(i)σ_i, and the limit magneticFieldFunctional(ν,b,ξ) is defined as the limit of variational values for simple-function approximations of the field law ξ, computed using the R-transform-type function of ν at edge b.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InvariantIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InvariantIsing.lean; bytes 13603..15051
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

theorem limiting_wasserstein_field_pressure_of_extreme_limits_unconditional :
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
      atTop (𝓝 ν))
    (field : (N : ℕ) → Fin N → ℝ) (ξ : ProbabilityMeasure ℝ)
    (_hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ))
    (_hw : Tendsto (fun k => fieldWassersteinOne (empiricalSpectralLaw (Nat.succ_pos k) (field (k+1))) ξ)
      atTop (𝓝 0)),
    Tendsto (fun N => ∫ ω, rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (field N) ∂P)
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (eig N) (matrixRotation (U N ω)⁻¹) (field N))
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) := by
  sorry

end InvariantIsing
end
end OAI
