-- Prove2me | Theorems.Thm_Kyprianou_exercise2_7_AllPartsCh02V3
-- name    : Kyprianou.exercise2_7_AllPartsCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:26:18.39687+00:00
-- url     : https://prove2.me/theorems/38e63dd3-adcd-4a67-9720-963452efddea
-- title:
--   Exercise 2.7: jump magnitude, path continuity, finite activity and density
-- statement:
--   Four parts: corrected strict jump threshold probability using Pi({|x|>a}); continuity exactly when jump intensity vanishes; piecewise linear paths exactly for compound Poisson with drift; and dense jump times under infinite activity. The strict-threshold correction excludes atoms at the boundary.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.7, pp. 62-66; corrections tracked in source-issues.json

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou
theorem exercise2_7_AllPartsCh02V3
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    :
    let piecewiseLinear : (ℝ≥0 → ℝ) → Prop := fun f =>
      ∃ (T : ℕ → ℝ≥0), T 0 = 0 ∧ StrictMono T ∧
        Tendsto T atTop atTop ∧
        ∀ n : ℕ, ∃ (slope intercept : ℝ),
          ∀ t : ℝ≥0, T n ≤ t → t < T (n + 1) →
            f t = slope * (t : ℝ) + intercept
    (∀ (t : ℝ≥0) (threshold : ℝ), 0 < threshold →
      P {ω | ∃ s : ℝ≥0, 0 < s ∧ s ≤ t ∧
        ∃ l : ℝ,
          Tendsto (fun u => X u ω)
            (nhdsWithin s (Set.Iio s)) (nhds l) ∧
          threshold < |X s ω - l|} =
      ENNReal.ofReal (1 -
        Real.exp (-(t : ℝ) *
          (ν {x : ℝ | threshold < |x|}).toReal))) ∧
    ((∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) ↔
      ν = 0) ∧
    ((∀ᵐ ω ∂P, piecewiseLinear (fun t => X t ω)) ↔
      σ = 0 ∧ ν Set.univ < ⊤) ∧
    (ν Set.univ = ⊤ →
      ∀ᵐ ω ∂P,
        closure {t : ℝ≥0 |
          ¬ ContinuousAt (fun s : ℝ≥0 => X s ω) t} =
          Set.univ)
      := by sorry
end Kyprianou
