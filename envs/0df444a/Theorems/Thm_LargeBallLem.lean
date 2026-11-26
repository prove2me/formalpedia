-- Prove2me | Theorems.Thm_LargeBallLem
-- name    : LargeBallLem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:41.985307+00:00
-- url     : https://prove2.me/theorems/3e38988c-6a6b-5938-9a3b-71f85e1094e7
-- title:
--   Large Ball Lem: Large Ball Lem
-- statement:
--   Paper Lemma 3.4 (line 677), stated pointwise: for a `(δ,ε)`-large-scale-invertible curve `γ`
--   and any `r ≥ δ/2`, the ball `B_r(x)` has `μ_γ`-measure at most `4(1+ε⁻¹)r`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/LargeBallLem.lean#L11-L96
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/LargeBallLem.lean#L11-L96

import Definitions.Def_Tablet_DGammaBallMeasure
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_LargeBallLem
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_DGammaBallMeasure

set_option autoImplicit false
open MeasureTheory Set ENNReal

theorem LargeBallLem {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hlsi : IsLSI γ δ ε) (x : E) (r : ℝ)
    (hr : δ / 2 ≤ r) :
    curveMeasure γ (Metric.closedBall x r) ≤ ENNReal.ofReal (4 * (1 + ε⁻¹) * r) := by sorry
