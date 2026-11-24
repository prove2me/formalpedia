-- Prove2me | Theorems.Thm_GlobalTheory_UnfoldNormal_map_swap_map_shear
-- name    : GlobalTheory.UnfoldNormal.map_swap_map_shear
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:24:36.91043+00:00
-- url     : https://prove2.me/theorems/8413ede9-3df3-4362-920e-23a45f33a032
-- title:
--   Unfold Normal: map swap map shear
-- statement:
--   The Unfold Normal construction uses the map swap map shear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapSwapShearedProductMeasureUnimodular.lean#L8-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapSwapShearedProductMeasureUnimodular.lean#L8-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapSwapShearedProductMeasureUnimodular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
open GlobalTheory GlobalTheory.UnfoldNormal

theorem GlobalTheory.UnfoldNormal.map_swap_map_shear (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H]
    [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H) (hNc : IsClosed (N : Set H))
    (κ : Measure N) (hκ : κ.IsHaarMeasure) (hinv : κ.map (fun n => n⁻¹) = κ) :
    ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap
      = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by sorry
