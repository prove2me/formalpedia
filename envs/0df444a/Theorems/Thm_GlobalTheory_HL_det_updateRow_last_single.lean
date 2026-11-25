-- Prove2me | Theorems.Thm_GlobalTheory_HL_det_updateRow_last_single
-- name    : GlobalTheory.HL.det_updateRow_last_single
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:15:43.096577+00:00
-- url     : https://prove2.me/theorems/cf1ec542-28e7-45d2-82b6-6652a36aa584
-- title:
--   HL: det update Row last single
-- statement:
--   The HL construction uses the det update Row last single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetGramTwoFrames.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetGramTwoFrames.lean#L30-L44

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
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
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.det_updateRow_last_single {R : Type} [CommRing R] (r : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (t : R) :
    (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) t)).det =
      t * (Z.submatrix Fin.castSucc Fin.castSucc).det := by sorry
