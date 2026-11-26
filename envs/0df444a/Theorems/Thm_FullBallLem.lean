-- Prove2me | Theorems.Thm_FullBallLem
-- name    : FullBallLem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:14.056326+00:00
-- url     : https://prove2.me/theorems/3911e49e-c76b-4897-a070-fb35314abd4f
-- title:
--   Full Ball Lem: Full Ball Lem
-- statement:
--   Paper Lemma 3.7 (line 743): for `γ` both a `(δ,ε,n)`-curve (`IsDeltaEpsN`, using its
--   closed-curve wrap-around arc clause) and `(δ,ε)`-large-scale-invertible, `γ`'s Morrey norm is at
--   most `4ε⁻¹+2n+4`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/FullBallLem.lean#L17-L327
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/FullBallLem.lean#L17-L327

import Definitions.Def_Tablet_LargeBallLem
import Definitions.Def_Tablet_DGammaBallMeasure
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_BigEdgeWindowPacking
import Definitions.Def_Tablet_StraddleAtMostOneEdge
import Definitions.Def_Tablet_ResolutionCoverBallMeasure
import Definitions.Def_Tablet_ArcLocalization
import Definitions.Def_Tablet_FullBallLem
import Theorems.Thm_ArcLocalization
import Theorems.Thm_BigEdgeWindowPacking
import Theorems.Thm_C1SmallBall
import Theorems.Thm_DGammaBallMeasure
import Theorems.Thm_LargeBallLem
import Theorems.Thm_ResolutionCoverBallMeasure
import Theorems.Thm_StraddleAtMostOneEdge

set_option autoImplicit false
open MeasureTheory Set ENNReal

theorem FullBallLem {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (δ ε : ℝ) (n : ℕ) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε < 1)
    (hden : IsDeltaEpsN γ δ ε n) (hlsi : IsLSI γ δ ε) :
    morreyNorm (curveMeasure γ) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 4) := by sorry
