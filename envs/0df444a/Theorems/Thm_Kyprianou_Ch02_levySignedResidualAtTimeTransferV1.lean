-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levySignedResidualAtTimeTransferV1
-- name    : Kyprianou.Ch02.levySignedResidualAtTimeTransferV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:28:45.765802+00:00
-- url     : https://prove2.me/theorems/16f520cb-d7ba-4b7c-979c-defdfbbc2ad6
-- title:
--   Transfer the signed jump residual at a fixed time under equal Levy path laws
-- statement:
--   Use the Proved globally measurable signed jump-series functional on absolutely summable cadlag paths. The equality event for the coordinate and this functional is measurable in path space. Equality of path pushforward laws transfers its conull property. Use each process cadlag and absolute summability to identify the functional with the actual signed jumps.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; canonical finite first moment model and equality of real Levy path laws.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levySignedResidualAtTimeTransferV1
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hpath : Measure.map (fun ω : Ω => fun t : ℝ≥0 => X t ω) P =
      Measure.map (fun ω : Λ => fun t : ℝ≥0 => Y t ω) Q)
    (T : ℝ≥0) (d : ℝ)
    (hXs : ∀ᵐ ω ∂P, Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
      |X (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|))
    (hYs : ∀ᵐ ω ∂Q, Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
      |Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)|))
    (hYeq : ∀ᵐ ω ∂Q, Y T ω = d * (T : ℝ) +
      ∑' s : Set.Ioc (0 : ℝ≥0) T,
        (Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0))) :
    ∀ᵐ ω ∂P, X T ω = d * (T : ℝ) +
      ∑' s : Set.Ioc (0 : ℝ≥0) T,
        (X (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)) := by
  sorry
