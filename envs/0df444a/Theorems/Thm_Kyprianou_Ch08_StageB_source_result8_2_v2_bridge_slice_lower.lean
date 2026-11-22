-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_slice_lower
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_slice_lower
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T18:22:06.676584+00:00
-- url     : https://prove2.me/theorems/795c944f-7070-4a09-b77f-8e35067898de
-- title:
--   Bridge 8.2 helper: lower slice bound for up-before-down excursion exponential
-- statement:
--   For the 8.2 excursion-exponential bridge, each thin slice from l to l+d admits the lower bound exp(-d*(Phi+tail(l))) ≤ u(l,l+d). This discharges frontier group E01 (L97) of parent candidate 45943 on bridge efd9aabc. Proof route: NoDrawdown N(d,l) ⊆ up-before-down U via sInf witness plus drawdown estimate, ruling out equal finite clocks with strict exit geometry on the shifted cadlag path (no positive jumps), then integral monotonicity against the height-law identity. The parent bridge applies this with the upper slice and limit child.
-- source:
--   Isolates the lower slice obligation of Kyprianou.Ch08.StageB.source_result8_2_v2_up_before_down_excursion_exponential [efd9aabc-cb4e-4443-a2e5-0c09c61782a3] after technical-only repair 45943 confirmed the clean 3-group mathematical frontier (10→3 strict-subset). Single-file genuine slice+limit proof blocked by complexity_risk guard (0.1908/0.1944 vs cutoff -0.0523); minimum source-faithful decomposition with identical parent context.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_slice_lower
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (q : ℝ) (hq : 0 ≤ q) (n : Measure ℝ)
    (hLaw : HasActualQExcursionHeightLaw P D ψ q n) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      Real.exp (-(d * (Phi ψ q + (n (Set.Ici l)).toReal))) ≤
        upBeforeDownExpectation P D.X q l (l + d) := by
  sorry
