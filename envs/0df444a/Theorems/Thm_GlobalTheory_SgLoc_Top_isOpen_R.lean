-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_Top_isOpen_R
-- name    : GlobalTheory.SgLoc.Top.isOpen_R
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:09:52.149135+00:00
-- url     : https://prove2.me/theorems/fa170248-a852-4034-b7be-0b9b4bfb5580
-- title:
--   Top: is Open R
-- statement:
--   The Top construction uses the is Open R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures.lean#L249-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures.lean#L249-L277

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [MeasurableSpace E]

theorem GlobalTheory.SgLoc.Top.isOpen_R [IsNonarchimedeanLocalField F] [CharZero F] (M : Model F E) :
    IsOpen (M.R : Set E) := by sorry
