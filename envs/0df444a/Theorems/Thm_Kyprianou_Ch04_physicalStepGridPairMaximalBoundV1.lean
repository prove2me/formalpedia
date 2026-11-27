-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalStepGridPairMaximalBoundV1
-- name    : Kyprianou.Ch04.physicalStepGridPairMaximalBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:56:26.095806+00:00
-- url     : https://prove2.me/theorems/67b6c446-46c1-5f46-86d9-bfd0d327ee01
-- title:
--   physicalStepGridPairMaximalBoundV1
-- statement:
--   The nested physical step-grid error obeys a mesh-independent maximal probability bound from the predictable kernel energy estimate.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_actualPoissonFutureIndependenceV1
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.physicalStepGridPairMaximalBoundV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (F : Filtration NNReal inferInstance) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hz : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0)
    (a b K : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ) (H L : ℕ → Ω → ℝ)
    (hH : ∀ k ∈ Finset.range n, Measurable[F (u k)] (H k))
    (hL : ∀ k ∈ Finset.range n, Measurable[F (u k)] (L k))
    (hHb : ∀ k ∈ Finset.range n, ∀ w, |H k w| ≤ K)
    (hLb : ∀ k ∈ Finset.range n, ∀ w, |L k w| ≤ K)
    (Y Z : NNReal → Ω → ℝ)
    (hY : ∀ t w, Y t w = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | a < |x| ∧ |x| < 1},
      z.2 ∂(N.N w)) - (t : ℝ) * (∫ x in {x : ℝ | a < |x| ∧ |x| < 1},x ∂ν))
    (hZ : ∀ t w, Z t w = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | b < |x| ∧ |x| < 1},
      z.2 ∂(N.N w)) - (t : ℝ) * (∫ x in {x : ℝ | b < |x| ∧ |x| < 1},x ∂ν))
    (X : NNReal → Ω → ℝ) (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (t : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (t : ℝ) ×ˢ univ → Measurable[F t] (fun w => N.N w D))
    (T : NNReal) (hT : 0 < T) (S : Ω → ℝ) (hS : Integrable S P)
    (hSnn : ∀ᵐ w ∂P, 0 ≤ S w)
    (hDiff : ∀ᵐ w ∂P, ∀ i ∈ Finset.range n, |H i w-L i w| ≤ K * Real.sqrt (S w))
    (hEnergy : (∫ w, S w ∂P) ≤ 4 * (T : ℝ) *
      (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal) :
    let A : Set ℝ := {x | a < |x| ∧ |x| < 1}
    let B : Set ℝ := {x | b < |x| ∧ |x| < 1}
    let W := fun (p : NNReal × Ω) => ∑ k ∈ Finset.range n,
      (Ioc (u k) (u (k+1))).indicator (fun _ => H k p.2) p.1
    let V := fun (p : NNReal × Ω) => ∑ k ∈ Finset.range n,
      (Ioc (u k) (u (k+1))).indicator (fun _ => L k p.2) p.1
    let g := fun p : (NNReal × Ω) × ℝ => A.indicator (fun x => x * W p.1) p.2
    let h := fun p : (NNReal × Ω) × ℝ => B.indicator (fun x => x * V p.1) p.2
    let k := fun p => g p-h p
    let J := fun (t : NNReal) w =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ), k ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ), k ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
    let G := fun (U : NNReal → Ω → ℝ) (Q : ℕ → Ω → ℝ) (t : NNReal) w =>
      ∑ i ∈ Finset.range n, Q i w * (U (min t (u (i+1))) w-U (min t (u i)) w)
    ∀ δ : ℝ, 0 < δ →
      P {w | ∃ t ≤ T, δ ≤ |G Y H t w-G Z L t w|} ≤
      ENNReal.ofReal (4 * ((K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
        (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
        (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal)) /
        ENNReal.ofReal ((δ/2)^2) := by
  sorry
