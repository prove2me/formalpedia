-- Prove2me | Theorems.Thm_InitialDeltaExists
-- name    : InitialDeltaExists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:21.531856+00:00
-- url     : https://prove2.me/theorems/303ad427-88cb-4222-921c-9411b87bb6e6
-- title:
--   Initial Delta Exists: Initial Delta Exists
-- statement:
--   Every closed piecewise-geodesic curve of positive length admits a starting scale `δ > 0` for
--   the surgery algorithm: `δ` has no small edges at all (`smallPieceCount γ δ = 0`), so in particular
--   `γ` is trivially a `(δ,ε,0)`-curve.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/InitialDeltaExists.lean#L13-L47
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/InitialDeltaExists.lean#L13-L47

import Definitions.Def_Tablet_StrictResolutionExists
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_InitialDeltaExists
import Theorems.Thm_StrictResolutionExists

set_option autoImplicit false
open Set

theorem InitialDeltaExists {E : Type*} [MetricSpace E] (γ : Curve E) (hpg : IsPiecewiseGeodesic γ)
    (hclosed : IsClosedCurve γ) (hlen : 0 < γ.len) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ smallPieceCount γ δ = 0 ∧ IsDeltaEpsN γ δ ε 0 := by sorry
