-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_bv_exit_ratio_no_standing_public
-- name    : Kyprianou.Ch08.StageB.source_result81_bv_exit_ratio_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T19:09:27.446835+00:00
-- url     : https://prove2.me/theorems/1721541d-480a-4b40-ad9b-b45bbfc3789f
-- title:
--   Bounded-variation two-sided exit ratio without the Avram standing assumptions
-- statement:
--   For a spectrally negative Lévy process of bounded variation, started at x in [0,a], the discounted transform of an upward exit from (0,a) before ruin equals Wq(x)/Wq(a). The proof uses the positive right root of the Laplace exponent and the q-scale property; it does not invoke the paper's additional standing regularity condition.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1 exit identity at positive discount. Isolates the bounded-variation Avram exit-ratio branch needed by source_result81_upper_positive_discount; the positive-root and scale hypotheses replace the stronger Standing premise used in the published Avram helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem Kyprianou.Ch08.StageB.source_result81_bv_exit_ratio_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : A.ψ φ = q)
    (W : ℝ → ℝ) (hW : AvramDividend.Classical.IsScaleFunction A q W)
    (hBV : A.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    AvramDividend.Classical.twoSidedExitExpectation A q a x =
      ENNReal.ofReal (W x / W a) := by sorry
