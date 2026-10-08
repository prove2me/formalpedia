-- Prove2me | Theorems.Thm_OAI_InvariantIsing_ground_state_limit_unconditional
-- name    : OAI.InvariantIsing.ground_state_limit_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:47.668204+00:00
-- url     : https://prove2.me/theorems/31f87a35-33fe-431b-b3a9-278f61fa1b5f
-- statement:
--   The theorem states that, for a probability space (Ω,P) and for each N a measurable random orthogonal N×N matrix U_N whose law on the orthogonal group is invariant under right multiplication (a Haar-type invariance), together with deterministic real eigenvalue lists eig_N(1..N), a probability measure ν on ℝ and reals a,b, the following holds under these assumptions: the support of ν lies in [a,b] and contains both a and b; for every ε>0, for all sufficiently large N every eigenvalue satisfies a−ε ≤ eig_N(i) ≤ b+ε; and the empirical spectral laws (1/N)Σ_i δ_{eig_N(i)} converge weakly to ν. Then there exists a real number M such that three things hold. First, the expectation under P of the normalized ground-state energy converges to M as N→∞, where this energy is (1/N) times the maximum over spin configurations σ∈{±1}^N of (1/2)Σ_i eig_N(i)·(R σ)_i², with R the rotation given by the inverse of U_N(ω) acting on the spin vector. Second, almost surely in ω, that same normalized ground-state energy converges to M. Third, the thermal variational value of ν with field parameter b, which is the variational functional (an extended-real value, converted to a real number) built from the scaled spectral law at inverse temperature β divided by β, converges to M as β→∞.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InvariantIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InvariantIsing.lean; bytes 16254..17278
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

theorem ground_state_limit_unconditional :
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (N : ℕ) → Ω → Orthogonal N) (_hU : ∀ N, Measurable (U N))
    (_hHaar : ∀ N, (P.map (U N)).IsMulRightInvariant)
    (eig : (N : ℕ) → Fin N → ℝ) (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (_hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (_ha : a∈(ν : Measure ℝ).support) (_hb : b∈(ν : Measure ℝ).support)
    (_hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (_hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1)))
      atTop (𝓝 ν)),
    ∃ M : ℝ,
      Tendsto (fun N => ∫ ω, groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹) ∂P)
        atTop (𝓝 M) ∧
      (∀ᵐ ω ∂P, Tendsto (fun N => groundStateEnergy (eig N) (matrixRotation (U N ω)⁻¹))
        atTop (𝓝 M)) ∧
      Tendsto (thermalVariationalValue ν b) atTop (𝓝 M) := by
  sorry

end InvariantIsing
end
end OAI
