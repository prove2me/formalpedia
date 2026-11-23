-- Prove2me | Theorems.Thm_GlobalTheory_HaarRightTranslate_map_mul_right_eq_modular
-- name    : GlobalTheory.HaarRightTranslate.map_mul_right_eq_modular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:10.295028+00:00
-- url     : https://prove2.me/theorems/53192800-2386-4c4b-a5d3-b875eb842d11
-- title:
--   Haar Right Translate: map mul right eq modular
-- statement:
--   The Haar Right Translate construction uses the map mul right eq modular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarLintegralMulRightLe.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarLintegralMulRightLe.lean#L13-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarLintegralMulRightLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.HaarRightTranslate
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem GlobalTheory.HaarRightTranslate.map_mul_right_eq_modular (μ : Measure H) [IsHaarMeasure μ] (g : H) :
    map (· * g) μ = modularCharacterFun g • μ := by sorry
