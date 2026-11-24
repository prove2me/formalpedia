-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyMonotoneForcesNonnegativeBVDriftV1
-- name    : Kyprianou.Ch02.levyMonotoneForcesNonnegativeBVDriftV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:34:32.199666+00:00
-- url     : https://prove2.me/theorems/9c19bb6e-0c25-47c2-a323-809c347e0118
-- title:
--   Monotone finite-variation Lévy paths force nonnegative uncompensated drift
-- statement:
--   Use the actual finite-variation Lévy path representation and identify the linear residual with the signed exponent drift after removing small-jump compensation. For a nondecreasing cadlag path its continuous Stieltjes residual after subtracting its jump atoms is nondecreasing; the residual drift must be nonnegative.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; necessity of the subordinator triplet conditions.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyMonotoneForcesNonnegativeBVDriftV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ))
    (hm : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω))
    (hσ : σ = 0)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure)
    (hsupport : levyMeasure (Set.Iio (0 : ℝ)) = 0) :
    0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure := by
  sorry
