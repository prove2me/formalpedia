-- Prove2me | Theorems.Thm_GlobalTheory_T_localModel_modulus_properties_on_units
-- name    : GlobalTheory.T.localModel_modulus_properties_on_units
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:52:44.630673+00:00
-- url     : https://prove2.me/theorems/ed3e201b-66e2-444f-bcd2-f9b831bb28f2
-- title:
--   T: local Model modulus properties on units
-- statement:
--   The T construction uses the local Model modulus properties on units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalModelModulusPropertiesOnUnitsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalModelModulusPropertiesOnUnitsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalModelModulusPropertiesOnUnits
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalModelModulusPropertiesOnUnitsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.localModel_modulus_properties_on_units : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → (∀ x y : E, IsUnit x → IsUnit y → M.modK (x * y) = M.modK x * M.modK y) ∧ (∀ x : E, IsUnit x → 0 < M.modK x ∧ M.modK (M.L.cj x) = M.modK x) ∧ ∀ x : E, x ∈ M.L.O → (∃ y ∈ M.L.O, x * y = 1) → M.modK x = 1 := by sorry
