-- Prove2me | Theorems.Thm_GeodesicMorreyLeTwo
-- name    : GeodesicMorreyLeTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:08:36.249401+00:00
-- url     : https://prove2.me/theorems/bda5318a-54c3-4ad1-8352-92c7cce65d1e
-- title:
--   Geodesic Morrey Le Two: Geodesic Morrey Le Two
-- statement:
--   The Geodesic Morrey Le Two construction uses the Geodesic Morrey Le Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/GeodesicMorreyLeTwo.lean#L9-L55
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/GeodesicMorreyLeTwo.lean#L9-L55

import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_IsGeodesicOn
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open MeasureTheory Set ENNReal

theorem GeodesicMorreyLeTwo {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (a b : ℝ) (hab : a ≤ b) (hbnd : b ≤ γ.len) (hgeo : IsGeodesicOn γ a b) :
    morreyNorm (Measure.map γ.toFun (volume.restrict (Set.Icc a b))) ≤ 2 := by sorry
