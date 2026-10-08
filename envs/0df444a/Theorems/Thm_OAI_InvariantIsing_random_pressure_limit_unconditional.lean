-- Prove2me | Theorems.Thm_OAI_InvariantIsing_random_pressure_limit_unconditional
-- name    : OAI.InvariantIsing.random_pressure_limit_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:48.391373+00:00
-- url     : https://prove2.me/theorems/db13bb1c-2201-4207-b0ed-b33117ebd7ee
-- statement:
--   The theorem states that, on a probability space (Ω, P), one has for each N a measurable random spectrum eig_N : Ω → ℝ^N and a measurable real random variable Y_N, together with a probability measure H_N on the orthogonal group O(N) that is invariant under right multiplication. Each Y_N is assumed to satisfy the conditional field-orbit law with zero external field: the joint law of (eig_N, 0, Y_N) is that obtained by drawing the spectrum from its law, drawing an independent H_N-distributed orthogonal matrix U, and setting the value to the rotated Ising pressure (1/N) log of the average over spin configurations σ in {±1}^N of exp((1/2) Σ_i eig_i (U⁻¹σ)_i² + field energy), where the field energy vanishes. Let ν be a probability measure on ℝ whose support is compact, contained in [a,b], and contains both a and b. Assume that the empirical spectral laws of eig_{k+1} converge in probability, in the Lévy–Prokhorov metric, to ν as k → ∞; that the spectral excess of eig_{k+1} relative to [a,b], namely the largest of 0 and the amounts by which eigenvalues fall below a or above b, tends to 0 in probability; and that the sequence (Y_{k+1}) is uniformly integrable in L¹(P). Then, writing L for the real-number value (toReal) of the variational functional applied to the function measureR(ν, b), which for x>0 is the inverse of the resolvent e ↦ ∫ 1/(e−y) dν(y), taken at x over e>b with default b, minus 1/x, and for x≤0 is the mean of ν, the sequence Y_{k+1} converges to the constant L in probability, converges to L in L¹ (the L¹ norm of Y_{k+1} − L tends to 0), and its expectations ∫ Y_{k+1} dP converge to L. The theorem is stated with its proof admitted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InvariantIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InvariantIsing.lean; bytes 18443..19937
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

theorem random_pressure_limit_unconditional :
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ)
    (_heig : ∀ N, Measurable (eig N)) (_hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (_hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hcompact : IsCompact (ν : Measure ℝ).support)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hweak : TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω))) atTop
      (fun _ => LevyProkhorov.ofMeasure ν))
    (_hexcess : TendstoInMeasure P (fun k ω => spectralExcess (eig (k+1) ω) a b)
      atTop (fun _ => 0))
    (_hUI : UniformIntegrable (fun k => Y (k+1)) 1 P),
    TendstoInMeasure P (fun k => Y (k+1)) atTop
      (fun _ => (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) ∧
    Tendsto (fun k => eLpNorm (fun ω => Y (k+1) ω-
      (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, Y (k+1) ω ∂P) atTop
      (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  sorry

end InvariantIsing
end
end OAI
