-- Prove2me | Theorems.Thm_GeodesicSampledCurrent
-- name    : GeodesicSampledCurrent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:13.448895+00:00
-- url     : https://prove2.me/theorems/8c50154f-c844-5402-acfe-e40d93fd8c87
-- title:
--   Geodesic Sampled Current: Geodesic Sampled Current
-- statement:
--   The piecewise-geodesic sampling `γ^δ` of `γ` at scale `δ` (`curveSampling`) is no longer than
--   `γ`, and its current differs from that of `γ` by at most `Lip(f) · Lip(π) · δ · len(γ)`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/GeodesicSampledCurrent.lean#L13-L199
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/GeodesicSampledCurrent.lean#L13-L199

import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentConcatAdditive
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_GeodesicSampledCurrent
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentConcatAdditive
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_RestrictCurrentFormula

set_option autoImplicit false

theorem GeodesicSampledCurrent {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlen : δ < γ.len) (ω : Form1 E) :
    (curveSampling GP γ δ hδ0 hδlen).len ≤ γ.len ∧
      |curveCurrent (curveSampling GP γ δ hδ0 hδlen) ω - curveCurrent γ ω|
        ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * δ * γ.len := by sorry
