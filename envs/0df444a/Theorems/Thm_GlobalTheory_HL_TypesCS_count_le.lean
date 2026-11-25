-- Prove2me | Theorems.Thm_GlobalTheory_HL_TypesCS_count_le
-- name    : GlobalTheory.HL.TypesCS.count_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:36:50.472147+00:00
-- url     : https://prove2.me/theorems/2957f990-1e89-4e42-a433-1c5dad11eda2
-- title:
--   Types CS: count le
-- statement:
--   The Types CS construction uses the count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AmpSqLeOfHermitianTermTypesCauchySchwarz.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AmpSqLeOfHermitianTermTypesCauchySchwarz.lean#L14-L25

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexEqCardMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AmpSqLeCardMulSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AmpSqLeOfHermitianTermTypesCauchySchwarz
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TypesCS

theorem GlobalTheory.HL.TypesCS.count_le (r a : ℕ) (H : ℝ) (ha : 1 ≤ a) (hH : (2 : ℝ) ^ a ≤ H) :
    ((a + a * (r * a) : ℕ) : ℝ) ≤ H ^ (r + 2) := by sorry
