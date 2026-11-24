-- Prove2me | Theorems.Thm_GlobalTheory_ModuleUnits_modK_units
-- name    : GlobalTheory.ModuleUnits.modK_units
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:59.702724+00:00
-- url     : https://prove2.me/theorems/e948150a-d794-45e3-828f-cd1f1d6f3fe9
-- title:
--   Module Units: mod K units
-- statement:
--   The Module Units construction uses the mod K units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalModelModulusPropertiesOnUnits.lean#L10-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalModelModulusPropertiesOnUnits.lean#L10-L87

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalModelModulusPropertiesOnUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc MeasureTheory
open scoped Pointwise ENNReal Classical NNReal
open GlobalTheory GlobalTheory.ModuleUnits

theorem GlobalTheory.ModuleUnits.modK_units : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → (∀ x y : E, IsUnit x → IsUnit y → M.modK (x * y) = M.modK x * M.modK y) ∧ (∀ x : E, IsUnit x → 0 < M.modK x ∧ M.modK (M.L.cj x) = M.modK x) ∧ ∀ x : E, x ∈ M.L.O → (∃ y ∈ M.L.O, x * y = 1) → M.modK x = 1 := by sorry
