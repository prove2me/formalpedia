-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordExist_dual_eq
-- name    : GlobalTheory.HL.CoordExist.dual_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:58:57.111403+00:00
-- url     : https://prove2.me/theorems/f12b3c7d-5b12-4a16-af42-3de1e97d6119
-- title:
--   Coord Exist: dual eq
-- statement:
--   The Coord Exist construction uses the dual eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NotField.lean#L118-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NotField.lean#L118-L125

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordExist
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem GlobalTheory.HL.CoordExist.dual_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a : Fin (r + 1)) (j : Fin r) :
    H.h (A.f a) (A.es j) = if a = j.castSucc then 1 else 0 := by sorry
