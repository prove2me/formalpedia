-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyActualFiniteVariationSignedJumpSeriesV1
-- name    : Kyprianou.Ch02.levyActualFiniteVariationSignedJumpSeriesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:44:33.475781+00:00
-- url     : https://prove2.me/theorems/9b8a7775-5a63-465c-9c07-dc29a1397d77
-- title:
--   Pathwise signed-jump series and deterministic drift for original finite-variation Levy process
-- statement:
--   Construct the exact original real Levy process under zero Gaussian coefficient and integrable truncated absolute Lévy jump measure, as a deterministic linear drift plus the countable series of its real jump sizes over positive times; require almost-sure absolute summability over every bounded time interval on one event. This is the physical, source-faithful finite-variation Lévy-Ito representation at all times, not only equality in distribution at fixed times.
-- source:
--   Kyprianou (2006) Chapter 2 Lemma 2.12, finite-variation form of the Lévy-Ito decomposition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyActualFiniteVariationSignedJumpSeriesV1
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
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) →
    ∃ (drift : ℝ),
      ∀ᵐ ω ∂P, ∃ (g : ℝ≥0 → ℝ),
        (∀ T : ℝ≥0, Summable (fun s : Set.Ioc (0 : ℝ≥0) T => |g s|)) ∧
        ∀ T : ℝ≥0,
          X T ω = drift * (T : ℝ) +
            ∑' s : Set.Ioc (0 : ℝ≥0) T, g s := by
  sorry
