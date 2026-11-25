-- Prove2me | Theorems.Thm_GlobalTheory_HL_det_gram_two_frames
-- name    : GlobalTheory.HL.det_gram_two_frames
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:49.909332+00:00
-- url     : https://prove2.me/theorems/836ef550-2ad1-5b7f-b01c-fafc36f355b8
-- title:
--   HL: det gram two frames
-- statement:
--   The HL construction uses the det gram two frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetGramTwoFrames.lean#L90-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetGramTwoFrames.lean#L90-L107

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

theorem GlobalTheory.HL.det_gram_two_frames {R : Type} [CommRing R] (r : ℕ)
    (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (T T' : R) :
    (Matrix.fromBlocks (Matrix.single (Fin.last r) (Fin.last r) (-T)) Z Z'
      (Matrix.single (Fin.last r) (Fin.last r) (-T'))).det =
      (-1) ^ (r + 1) * (Z.det * Z'.det - T * T' *
        ((Z.submatrix Fin.castSucc Fin.castSucc).det *
          (Z'.submatrix Fin.castSucc Fin.castSucc).det)) := by sorry
