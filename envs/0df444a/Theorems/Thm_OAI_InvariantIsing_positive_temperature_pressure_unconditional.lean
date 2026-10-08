-- Prove2me | Theorems.Thm_OAI_InvariantIsing_positive_temperature_pressure_unconditional
-- name    : OAI.InvariantIsing.positive_temperature_pressure_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:48.10198+00:00
-- url     : https://prove2.me/theorems/a1be616a-73d3-49d0-88a8-57fa66f25b99
-- statement:
--   For a spin system on N Ising spins σ ∈ {−1,1}^N, the rotated pressure for eigenvalues λ₁,…,λ_N, an orthogonal rotation U and a field c is (1/N) times the log of the average over all 2^N spin configurations of exp(H(σ)), where H(σ) = (1/2)∑ᵢ λᵢ (Uσ)ᵢ² + ∑ᵢ cᵢσᵢ. The theorem states that, for any probability space (Ω,P), random N×N orthogonal matrices U_N that are measurable and whose laws are right-invariant under multiplication (Haar-type), and any deterministic eigenvalue arrays (eig_N,i), the following holds under these assumptions: ν is a probability measure on ℝ whose support lies in [a,b] and contains both a and b; for every ε>0, eventually in N all eigenvalues lie in [a−ε,b+ε]; the empirical spectral laws (1/N)∑ᵢ δ_{eig_N,i} converge weakly to ν; and the inverse temperature β is strictly positive. Then, with eigenvalues β·eig_N,i, rotation U_N(ω)⁻¹ and zero external field, the expected rotated pressure ∫ pressure dP converges as N → ∞, and the pressure itself converges for P-almost every ω, in both cases to the real part of the variational functional of the measureR transform of the β-rescaled law of ν, evaluated at the edge β·b.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InvariantIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InvariantIsing.lean; bytes 15053..16252
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

theorem positive_temperature_pressure_unconditional :
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (_hU : ∀ N, Measurable (U N))
    (_hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (β : ℝ) (_hβ : 0 < β)
    (_hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)),
    Tendsto (fun N => ∫ ω, rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0) ∂P)
      atTop (𝓝 (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal) ∧
    ∀ᵐ ω ∂P, Tendsto (fun N => rotatedPressure (fun i => β*eig N i) (matrixRotation (U N ω)⁻¹) (fun _ => 0))
      atTop (𝓝 (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal) := by
  sorry

end InvariantIsing
end
end OAI
