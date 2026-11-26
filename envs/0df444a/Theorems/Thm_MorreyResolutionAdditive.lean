-- Prove2me | Theorems.Thm_MorreyResolutionAdditive
-- name    : MorreyResolutionAdditive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:08:01.775462+00:00
-- url     : https://prove2.me/theorems/db511730-19f3-4c25-ae06-f0ac2b1a60a2
-- title:
--   Morrey Resolution Additive: Morrey Resolution Additive
-- statement:
--   The Morrey Resolution Additive construction uses the Morrey Resolution Additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MorreyResolutionAdditive.lean#L8-L42
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MorreyResolutionAdditive.lean#L8-L42

import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_MorreyResolutionAdditive
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open MeasureTheory Set

theorem MorreyResolutionAdditive {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (k : ℕ) (s : ℕ → ℝ)
    (hmono : MonotoneOn s (Set.Icc 0 k)) (h0 : s 0 = 0) (hk : s k = γ.len) :
    curveMeasure γ =
      ∑ i ∈ Finset.range k, Measure.map γ.toFun (volume.restrict (Set.Icc (s i) (s (i + 1)))) := by sorry
