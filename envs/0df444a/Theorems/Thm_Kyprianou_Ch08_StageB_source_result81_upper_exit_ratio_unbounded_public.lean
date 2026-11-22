-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio_unbounded_public
-- name    : Kyprianou.Ch08.StageB.source_result81_upper_exit_ratio_unbounded_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T19:08:59.130867+00:00
-- url     : https://prove2.me/theorems/d5341415-bb7f-4960-a072-c2b2517acc25
-- title:
--   Unbounded-variation two-sided exit ratio for a nonnegative start
-- statement:
--   For unbounded variation and a start in [0,a], the strict two-sided exit expectation equals the q-scale ratio. This uses the proved strict/corrected expectation identity and the proved corrected exit-ratio theorem.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1 equation (8.8). Isolates the unbounded-variation exit-ratio branch used by the source upper exit identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_upper_exit_ratio_unbounded_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : AvramDividend.Classical.IsScaleFunction A q W)
    (hnbv : ¬ A.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    AvramDividend.Classical.twoSidedExitExpectation A q a x =
      ENNReal.ofReal (W x / W a) := by sorry
