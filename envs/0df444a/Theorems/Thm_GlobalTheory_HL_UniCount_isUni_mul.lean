-- Prove2me | Theorems.Thm_GlobalTheory_HL_UniCount_isUni_mul
-- name    : GlobalTheory.HL.UniCount.isUni_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:20.641522+00:00
-- url     : https://prove2.me/theorems/3f31f42d-44c0-4eac-9cd4-b88227b259db
-- title:
--   Uni Count: is Uni mul
-- statement:
--   The Uni Count construction uses the is Uni mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUniCosetsLe.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUniCosetsLe.lean#L15-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.UniCount
variable {E : Type} [CommRing E] {N : ℕ}

theorem GlobalTheory.HL.UniCount.isUni_mul {s t : Matrix (Fin N) (Fin N) E} (hs : IsUni s) (ht : IsUni t) :
    IsUni (s * t) := by sorry
