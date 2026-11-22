-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_scale_transfer_public
-- name    : Kyprianou.Ch08.StageB.source_result81_upper_scale_transfer_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T19:09:22.124586+00:00
-- url     : https://prove2.me/theorems/83c742a9-2077-45a0-aec2-f0b3403985ae
-- title:
--   Transfer the Chapter 8 source q-scale to the filtered Avram model
-- statement:
--   The source q-scale transfers to the indistinguishable all-path Avram model because the two exponents agree on the nonnegative half-line, giving equal right-root sets and equal Laplace transforms there.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1 scale normalization. Isolates the scale-transfer obligation for the upper exit-ratio proof.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
open MeasureTheory ProbabilityTheory Filter Set Topology
open AvramDividend.Classical Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_upper_scale_transfer_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (ψ : ℝ → ℝ) (hexp : ∀ β : ℝ, 0 ≤ β → A.ψ β = ψ β)
    (hnotneg : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω)))
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hWq : Kyprianou.Ch08.IsQScale ψ q W) :
    AvramDividend.Classical.IsScaleFunction A q W := by sorry
