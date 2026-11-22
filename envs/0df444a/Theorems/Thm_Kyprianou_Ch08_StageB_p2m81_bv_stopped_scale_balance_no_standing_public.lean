-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_bv_stopped_scale_balance_no_standing_public
-- name    : Kyprianou.Ch08.StageB.p2m81_bv_stopped_scale_balance_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T22:03:53.095889+00:00
-- url     : https://prove2.me/theorems/3c45c728-d58f-45f0-8e2b-03db248a5056
-- title:
--   Standing-free bounded-variation stopped scale balance
-- statement:
--   For a spectrally negative Lévy process of bounded variation with a positive discount q, a positive root φ of the Laplace exponent, and a genuine q-scale function W, the discounted two-sided exit expectation multiplied by W(a) equals W(x) for 0 ≤ x ≤ a. This isolates the standing-free optional-stopping balance needed for the bounded-variation exit ratio in Kyprianou Chapter 8 Theorem 8.1.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1. Standing-free bounded-variation stopped scale balance isolated from source_result81_bv_exit_ratio_no_standing_public.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem Kyprianou.Ch08.StageB.p2m81_bv_stopped_scale_balance_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : A.ψ φ = q)
    (W : ℝ → ℝ) (hW : AvramDividend.Classical.IsScaleFunction A q W)
    (hBV : A.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    AvramDividend.Classical.twoSidedExitExpectation A q a x *
        ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by sorry
