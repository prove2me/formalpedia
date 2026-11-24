-- Prove2me | Theorems.Thm_GlobalTheory_T_map_swap_sheared_product_measure_unimodular
-- name    : GlobalTheory.T.map_swap_sheared_product_measure_unimodular
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:52:52.07832+00:00
-- url     : https://prove2.me/theorems/a5e4c6be-f792-4fe0-a1e8-0e6c134c057e
-- title:
--   T: map swap sheared product measure unimodular
-- statement:
--   The T construction uses the map swap sheared product measure unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapSwapShearedProductMeasureUnimodularStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapSwapShearedProductMeasureUnimodularStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapSwapShearedProductMeasureUnimodular
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapSwapShearedProductMeasureUnimodularStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.map_swap_sheared_product_measure_unimodular : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H), IsClosed (N : Set H) → ∀ (κ : Measure N), κ.IsHaarMeasure → κ.map (fun n => n⁻¹) = κ → ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by sorry
