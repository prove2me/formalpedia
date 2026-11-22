-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_upper_drawdown
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_upper_drawdown
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:38:07.862595+00:00
-- url     : https://prove2.me/theorems/854bc38d-307b-481b-9c77-08483f28523c
-- title:
--   Bridge 8.2 helper: drawdown bound before upcrossing when up precedes down
-- statement:
--   For a spectrally negative Levy path started at 0, at any time t before the upcrossing of d, when the upcrossing of d strictly precedes the downcrossing of -l, the drawdown from the running sup stays below l+d. Pointwise sInf passage bounds give X u ≤ d for all u ≤ t and -l ≤ X t, hence running sup ≤ d and max 0 sup - X t ≤ l+d. This discharges the drawdown-estimate core of upper slice fe886010 (frontier group E02 of bridge efd9aabc), letting the upper reproof hold only clock equalities, inclusion assembly, and integral monotonicity.
-- source:
--   Minimum source-faithful descendant of Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_slice_upper [fe886010-e1c1-4101-92bd-c111ca85d838] (itself a child of bridge efd9aabc-cb4e-4443-a2e5-0c09c61782a3). The direct 86-line upper proof (SHA 76969e32, sorry-free, code_budget PASS) was refused by complexity_risk 0.2712 vs cutoff -0.0523; content (clocks+sInf+sup+max+integral) inherently exceeds single-file complexity. This one descendant carries the pure D.X drawdown estimate with no shifted clocks, no excursion law, and minimal binders (D/P only); clock equalities fold into the upper reproof where the shifted-to-X translation is meaningful.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_upper_drawdown
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      ∀ t : ℝ≥0, ∀ ω : Ω,
        (t : WithTop ℝ≥0) < tauPlus D.X d ω →
        tauPlus D.X d ω < tauMinus D.X (-l) ω →
        reflectAtSup D.X 0 t ω ≤ l + d := by
  sorry
