-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_slice_upper
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_slice_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:22:13.046319+00:00
-- url     : https://prove2.me/theorems/fe886010-e1c1-4101-92bd-c111ca85d838
-- title:
--   Bridge 8.2 helper: upper slice bound for up-before-down excursion exponential
-- statement:
--   For the 8.2 excursion-exponential bridge, each thin slice admits the upper bound u(l,l+d) ≤ exp(-d*(Phi+tail(l+d+d))). This discharges frontier group E02 (L102) of parent candidate 45943 on bridge efd9aabc. Proof route (pointwise, no a.s.): clock equalities plus sInf bounds (X≤d before up, X≥-l before down, X0=0), running sup ≤d, drawdown ≤l+d<l+d+d, hence U⊆N(d,l+d+d), then integral monotonicity against the height-law identity. The parent bridge applies this with the lower slice and limit child.
-- source:
--   Isolates the upper slice obligation of bridge efd9aabc after 45943 confirmed the clean frontier. Minimum decomposition; identical parent context; single-file proof blocked by complexity guard.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_slice_upper
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (q : ℝ) (hq : 0 ≤ q) (n : Measure ℝ)
    (hLaw : HasActualQExcursionHeightLaw P D ψ q n) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      upBeforeDownExpectation P D.X q l (l + d) ≤
        Real.exp (-(d * (Phi ψ q + (n (Set.Ici (l + d + d))).toReal))) := by
  sorry
