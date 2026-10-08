-- Prove2me | Theorems.Thm_OAI_InvariantIsing_random_pressure_tendsto_ae_unconditional
-- name    : OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:48.538983+00:00
-- url     : https://prove2.me/theorems/361adfcf-737b-430f-a91a-40ea5c7f7251
-- statement:
--   The theorem states that, on a probability space (Ω, P), suppose that for each N one has a measurable random eigenvalue vector eig_N(ω) in ℝ^N and a measurable real random variable Y_N, and that H_N is a probability measure on the N×N orthogonal group that is invariant under right multiplication. Suppose the joint law of ((eig_N, 0), Y_N) (zero external field) coincides with the law obtained by drawing the spectral data (eig_N, 0) from its marginal law, drawing an independent U from H_N, and taking the rotated Ising pressure: (1/N) times the log of the average over spins σ in {±1}^N of exp(½ Σ_i eig_i (U⁻¹σ)_i² + Σ_i 0·σ_i), where the field vanishes. Let ν be a Borel probability measure on ℝ whose support is compact, contained in [a,b], and contains both a and b. Assume that almost surely, for every ε>0, eventually in N all entries of eig_N lie in [a−ε, b+ε], and that almost surely the empirical spectral measures (1/N)Σ_i δ_{eig_N,i}, indexed by N=k+1, converge weakly to ν. Then, almost surely, Y_N converges as N→∞ to the real number obtained by converting (via toReal) the extended-real variational functional evaluated at the function R obtained from ν and the edge b, namely R(x)=ℓ(x)−1/x for x>0, where ℓ(x) is the point e>b solving ∫1/(e−y)dν(y)=x when it exists (and b otherwise), and R(x)=∫y dν(y) for x≤0. That variational functional is the infimum over monotone overlap paths p:ℝ→[0,1] of an entropy functional plus ½∫R(deficit_p(r))dr over (0,1).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InvariantIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InvariantIsing.lean; bytes 19939..21067
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

theorem random_pressure_tendsto_ae_unconditional :
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
    (_hno : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ i, a-ε ≤ eig N ω i ∧ eig N ω i ≤ b+ε)
    (_hweak : ∀ᵐ ω ∂P, Tendsto (fun k =>
      empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω)) atTop (𝓝 ν)),
    ∀ᵐ ω ∂P, Tendsto (fun N => Y N ω) atTop
      (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  sorry

end InvariantIsing
end
end OAI
