-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cutoffCauchyFromTerminalEnergyV1
-- name    : Kyprianou.Ch04.cutoffCauchyFromTerminalEnergyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:24:52.830375+00:00
-- url     : https://prove2.me/theorems/7394422a-7b6a-5aa1-ad60-822fd7332f55
-- title:
--   Maximal cutoff Cauchy convergence from terminal energy and martingale regularity
-- statement:
--   Maximal cutoff Cauchy convergence from terminal energy and martingale regularity
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem cutoffCauchyFromTerminalEnergyV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (M : ℝ → NNReal → Ω → ℝ) (T : NNReal) (hT : 0 < T)
    (C : ℝ) (hM : ∀ e, 0 < e → e < 1 → Martingale (M e) F P)
    (hR : ∀ e, 0 < e → e < 1 → ∀ᵐ ω ∂P, ∀ t : NNReal,
      Tendsto (fun s => M e s ω) (𝓝[>] t) (𝓝 (M e t ω)))
    (hL2 : ∀ e, 0 < e → e < 1 → MemLp (M e T) 2 P)
    (hEnergy : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
      (∫ ω, (M a T ω - M b T ω)^2 ∂P) ≤ C *
        (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal) :
    (∀ e : ℝ, 0 < e → e < 1 →
      Integrable (fun ω => sSup ((fun t : NNReal => |M e t ω|^2) '' Iic T)) P) ∧
    ∀ δ : ℝ, 0 < δ → ∃ e0 : ℝ, 0 < e0 ∧ e0 < 1 ∧
      ∀ a b : ℝ, 0 < a → a < e0 → 0 < b → b < e0 →
        Integrable (fun ω => sSup ((fun t : NNReal => |M a t ω - M b t ω|^2) '' Iic T)) P ∧
        (∫ ω, sSup ((fun t : NNReal => |M a t ω - M b t ω|^2) '' Iic T) ∂P) < δ := by
  sorry
end Kyprianou.Ch04
