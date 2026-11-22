-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_scale_family_atoms_vanish
-- name    : Kyprianou.Ch08.StageB.p2m81_scale_family_atoms_vanish
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T00:22:19.270781+00:00
-- url     : https://prove2.me/theorems/bc9bed39-17f3-4022-9269-fabf57720fc3
-- title:
--   Scale-indexed drawdown laws and potentials with agreeing atoms and vanishing singletons
-- statement:
--   From the per-scale drawdown Laplace equations, select drawdown laws and build one-scale renewal potentials with Laplace s/f(s) and exact positive atoms (d/f d) times the drawdown singleton. All scales agree on every positive singleton by exponential tilting and finite-measure Laplace uniqueness. The ratio d/f(d) for d>=1 is bounded by 1/f(1) from the s=1 equation, and each fixed positive drawdown singleton tends to zero as the scale goes to infinity by the Laplace deficit Markov bound. Packages the exact facts the geometric descending potential bridge needs to squeeze atoms to zero.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_scale_family_atoms_vanish
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (hdraw : ∀ d : ℝ, 0 < d → ∃ ρ : Measure ℝ,
      IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d)) :
    ∃ (ρd νd : ℝ → Measure ℝ),
      (∀ d : ℝ, 0 < d →
        IsProbabilityMeasure (ρd d) ∧ (ρd d) (Iio (0 : ℝ)) = 0 ∧
        ∀ s : ℝ, 0 < s →
          (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρd d)).toReal =
            f d * (1 - s / d)) ∧
      (∀ d : ℝ, 0 < d →
        (νd d) (Iio (0 : ℝ)) = 0 ∧
        (∀ x : ℝ, 0 ≤ x → (νd d) (Iic x) < ⊤) ∧
        (∀ s : ℝ, 0 < s →
          (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(νd d)) =
            ENNReal.ofReal (s / f s)) ∧
        (∀ x : ℝ, 0 < x →
          (νd d) {x} = ENNReal.ofReal (d / f d) * (ρd d) {x})) ∧
      (∀ x : ℝ, 0 < x → ∀ d1 d2 : ℝ, 0 < d1 → 0 < d2 →
        (νd d1) {x} = (νd d2) {x}) ∧
      (∀ d : ℝ, 1 ≤ d → d / f d ≤ 1 / f 1) ∧
      (∀ x : ℝ, 0 < x →
        Tendsto (fun d : ℝ => (ρd d) {x}) atTop (nhds (0 : ℝ≥0∞))) := by
  sorry
