-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_Top_mem_integer_of_isIntegral
-- name    : GlobalTheory.SgLoc.Top.mem_integer_of_isIntegral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:09:57.934952+00:00
-- url     : https://prove2.me/theorems/233a6ae2-5eba-454b-a2c5-abcae59cded6
-- title:
--   Top: mem integer of is Integral
-- statement:
--   The Top construction uses the mem integer of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures.lean#L50-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures.lean#L50-L50

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.SgLoc.Top.mem_integer_of_isIntegral {a : F} (h : IsIntegral 𝒪[F] a) : a ∈ 𝒪[F] := by sorry
