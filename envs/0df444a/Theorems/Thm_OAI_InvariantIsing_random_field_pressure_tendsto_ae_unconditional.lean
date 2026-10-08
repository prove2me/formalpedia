-- Prove2me | Theorems.Thm_OAI_InvariantIsing_random_field_pressure_tendsto_ae_unconditional
-- name    : OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:48.238158+00:00
-- url     : https://prove2.me/theorems/904e96f1-7492-44b3-8465-6382647181d0
-- statement:
--   The theorem states that, on a probability space (Ω,P), suppose that for each N one has measurable random data d_N(ω)=(λ^N(ω),h^N(ω)) consisting of a spectrum λ^N in ℝ^N and a field vector h^N in ℝ^N, together with measurable real random variables Y_N. For each N let H_N be a right-invariant probability measure on the orthogonal group O(N). Assume that the joint law of (d_N,Y_N) equals the law of (d, pressure) where d has the law of d_N, U is drawn from H_N independently of d, and pressure is the formal rotated pressure of the data d with the rotation given by U⁻¹; this is the ConditionalFieldOrbitLaw hypothesis. Let ν be a probability measure on ℝ with compact support contained in [a,b], with both a and b lying in the support. Assume that almost surely, for every ε>0, eventually in N all spectral entries λ^N_i lie in [a-ε,b+ε], and that the empirical spectral laws (1/(k+1))∑ᵢ δ_{λ^{k+1}_i} of λ^{k+1} converge weakly to ν. Let ξ be a probability measure on ℝ with finite first moment, and assume that almost surely the Wasserstein-1 distance between the empirical law of the field entries h^{k+1} and ξ tends to 0 as k→∞. Then, almost surely, Y_N converges as N→∞ to magneticFieldFunctional(ν,b,ξ), the limiting magnetic-field functional of the spectral measure ν with right edge b and field law ξ, which is defined as a limit of finite-magnetization variational values along simple-function approximations of ξ. The statement is a theorem whose proof is admitted in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InvariantIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InvariantIsing.lean; bytes 21069..22404
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

theorem random_field_pressure_tendsto_ae_unconditional :
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : (N : ℕ) → Ω → FieldSpectralData N) (Y : ℕ → Ω → ℝ)
    (_hd : ∀ N, Measurable (d N)) (_hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (_hlaw : ∀ N, ConditionalFieldOrbitLaw P (d N) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hcompact : IsCompact (ν : Measure ℝ).support)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hno : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ i, a-ε ≤ (d N ω).1 i ∧ (d N ω).1 i ≤ b+ε)
    (_hweak : ∀ᵐ ω ∂P, Tendsto (fun k =>
      empiricalSpectralLaw (Nat.succ_pos k) (d (k+1) ω).1) atTop (𝓝 ν))
    (ξ : ProbabilityMeasure ℝ) (_hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ))
    (_hw : ∀ᵐ ω ∂P, Tendsto (fun k => fieldWassersteinOne
      (empiricalSpectralLaw (Nat.succ_pos k) (d (k+1) ω).2) ξ) atTop (𝓝 0)),
    ∀ᵐ ω ∂P, Tendsto (fun N => Y N ω) atTop
      (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) := by
  sorry

end InvariantIsing
end
end OAI
