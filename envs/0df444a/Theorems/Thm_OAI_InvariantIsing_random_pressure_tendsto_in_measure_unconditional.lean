-- Prove2me | Theorems.Thm_OAI_InvariantIsing_random_pressure_tendsto_in_measure_unconditional
-- name    : OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:48.684442+00:00
-- url     : https://prove2.me/theorems/35f32dc4-06aa-4d1e-a047-0c439cf1428b
-- statement:
--   The theorem states that, on a probability space (Ω,P), one has for each N a measurable random spectrum eig_N : Ω → ℝ^N and a measurable real random variable Y_N, together with a right-invariant Borel probability measure H_N on the orthogonal group O(N) (right invariance is assumed as a typeclass hypothesis). The law of the pair (eig_N, Y_N) is assumed to be a conditional orbit law with zero magnetic field: it equals the image of the product of the law of (eig_N, 0) with H_N under the map sending (data, U) to (data, rotated pressure), where the rotated pressure is (1/N) times the log of the average over spin configurations σ ∈ {±1}^N of exp((1/2) Σ_i eig_i (U⁻¹σ)_i²), with the orthogonal matrix U⁻¹ acting as a rotation of ℝ^N. Let ν be a Borel probability measure on ℝ whose support is compact and contained in [a,b], with both endpoints a and b belonging to the support. Assume two convergences in probability as k → ∞, indexed by N=k+1: the empirical spectral law (1/N)Σ_i δ_{eig_{N,i}} converges in measure to ν in the Lévy–Prokhorov metric, and the spectral excess max(0, max_i (a − eig_i), max_i (eig_i − b)), which measures how far the spectrum sticks out of [a,b], converges in measure to 0. The conclusion is that Y_{k+1} converges in measure under P to the constant real number obtained as the real value (toReal) of variationalFunctional applied to the function measureR(ν,b), that is, the infimum over overlap paths p (monotone functions ℝ → [0,1]) of the entropy functional of p plus the spectral functional of p. This is stated as an admitted theorem without extra regularity or edge-convergence conditions beyond those listed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InvariantIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InvariantIsing.lean; bytes 17280..18441
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

theorem random_pressure_tendsto_in_measure_unconditional
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ)
    (heig : ∀ N, Measurable (eig N)) (hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hweak : TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω))) atTop
      (fun _ => LevyProkhorov.ofMeasure ν))
    (hexcess : TendstoInMeasure P (fun k ω => spectralExcess (eig (k+1) ω) a b)
      atTop (fun _ => 0)) :
    TendstoInMeasure P (fun k => Y (k+1)) atTop
      (fun _ => (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  sorry

end InvariantIsing
end
end OAI
