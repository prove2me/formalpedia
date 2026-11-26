-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49AllPathDepthWitnessV1
-- name    : Kyprianou.Ch04.exercise49AllPathDepthWitnessV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:52:27.691838+00:00
-- url     : https://prove2.me/theorems/5362789c-e07d-4623-b289-9d92d91d6c7c
-- title:
--   Physical depth witnesses for measurable all-path càdlàg Levy processes
-- statement:
--   All-path specialization of the physical depth witness, sufficient by indistinguishability.
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49AllPathDepthWitnessV1
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] (X : NNReal → Omega → ℝ)
    (hLevy : IsLevyProcess X P) (hm : ∀ t, Measurable (X t))
    (hc : ∀ omega, IsCadlag (fun t => X t omega))
    (hTendsInfinity : ∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atTop) :
    let tau : Real → Omega → WithTop NNReal := fun initial omega =>
      sInf {v : WithTop NNReal | ∃ t : NNReal,
        v = ↑t ∧ 0 < t ∧ initial + X t omega < 0}
    ∀ (finiteTime : Omega → NNReal), Measurable finiteTime →
      (∀ᵐ omega ∂P, tau 0 omega ≠ ⊤ →
        tau 0 omega = (finiteTime omega : WithTop NNReal)) →
          ∃ (D : Set Omega) (I V W : Omega → ℝ),
            MeasurableSet D ∧ Measurable I ∧ Measurable V ∧ Measurable W ∧
            (P D = P {omega : Omega | tau 0 omega ≠ ⊤}) ∧
            (∀ B : Set Real, MeasurableSet B →
              P (I ⁻¹' B ∩ D) = P {omega : Omega | tau 0 omega ≠ ⊤ ∧
                -(X (finiteTime omega) omega) ∈ B}) ∧
            (∀ x : Real, 0 ≤ x →
              P (V ⁻¹' Set.Iic x) = P {omega : Omega | tau x omega = ⊤}) ∧
            (∀ᵐ omega ∂P.restrict Dᶜ, V omega = 0) ∧
            (∀ᵐ omega ∂P.restrict D, V omega = I omega + W omega) ∧
            Measure.map (fun omega => (I omega, W omega)) (P.restrict D) =
              (Measure.map I (P.restrict D)).prod (Measure.map V P) := by
  sorry
