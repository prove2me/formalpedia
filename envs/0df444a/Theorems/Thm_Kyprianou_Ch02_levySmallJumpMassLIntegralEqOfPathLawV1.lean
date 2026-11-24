-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levySmallJumpMassLIntegralEqOfPathLawV1
-- name    : Kyprianou.Ch02.levySmallJumpMassLIntegralEqOfPathLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:52:24.451796+00:00
-- url     : https://prove2.me/theorems/fb5881b1-c0d3-488b-903e-8f160baf00e4
-- title:
--   Equality of expected actual small-jump mass under equal Levy path laws
-- statement:
--   Use the Proved Borel functional for actual cadlag jump mass, the two Proved whole-path a.e. measurability results, and lintegral_map prime to transfer the nonnegative expected mass exactly through the common law. No moment finiteness is assumed.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levySmallJumpMassLIntegralEqOfPathLawV1
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hpath :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X t ω) P =
      Measure.map (fun ω : Λ => fun t : ℝ≥0 => Y t ω) Q)
    (T : ℝ≥0) :
    (∫⁻ ω : Ω, ∑' s : Set.Ioc (0 : ℝ≥0) T,
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) =
      (∫⁻ ω : Λ, ∑' s : Set.Ioc (0 : ℝ≥0) T,
        ENNReal.ofReal
          (if |Y (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |Y (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)|
           else 0) ∂Q) := by
  sorry
