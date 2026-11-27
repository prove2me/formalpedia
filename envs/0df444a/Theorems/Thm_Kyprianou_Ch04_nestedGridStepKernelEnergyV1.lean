-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nestedGridStepKernelEnergyV1
-- name    : Kyprianou.Ch04.nestedGridStepKernelEnergyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:56:25.745001+00:00
-- url     : https://prove2.me/theorems/cb9b7573-9764-40f9-b16e-9ec69ae85c94
-- title:
--   nestedGridStepKernelEnergyV1
-- statement:
--   Predictability and energy certificate for the nested cutoff grid kernel.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.nestedGridStepKernelEnergyV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (F : Filtration NNReal inferInstance) (a b K : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (T : NNReal) (W V : NNReal × Ω → ℝ)
    (hW : Measurable[F.predictable] W) (hV : Measurable[F.predictable] V)
    (hWb : ∀ p, |W p| ≤ K) (hVb : ∀ p, |V p| ≤ K)
    (S : Ω → ℝ) (hS : Integrable S P) (hSnn : ∀ᵐ w ∂P, 0 ≤ S w)
    (hDiff : ∀ᵐ w ∂P, ∀ t : NNReal, |W (t,w)-V (t,w)| ≤ K * Real.sqrt (S w))
    (hEnergy : (∫ w, S w ∂P) ≤ 4 * (T : ℝ) *
      (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal) :
    let A : Set ℝ := {z | a < |z| ∧ |z| < 1}
    let B : Set ℝ := {z | b < |z| ∧ |z| < 1}
    let g := fun p : (NNReal × Ω) × ℝ => A.indicator (fun z => z * W p.1) p.2
    let h := fun p : (NNReal × Ω) × ℝ => B.indicator (fun z => z * V p.1) p.2
    let k := fun p => g p-h p
    Measurable[F.predictable.prod inferInstance] g ∧
    Measurable[F.predictable.prod inferInstance] h ∧
    (∀ p, ‖g p‖ ≤ K ∧ ‖h p‖ ≤ K) ∧
    (∀ p, p.2 ∉ A → g p = 0 ∧ h p = 0) ∧
    (∫ w, ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ),
      (k ((z.1.toNNReal,w),z.2))^2 ∂referenceIntensity ν ∂P) ≤
      (K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
        (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
        (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal := by
  sorry
