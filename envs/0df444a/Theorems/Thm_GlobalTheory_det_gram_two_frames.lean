-- Prove2me | Theorems.Thm_GlobalTheory_det_gram_two_frames
-- name    : GlobalTheory.det_gram_two_frames
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:46.276795+00:00
-- url     : https://prove2.me/theorems/803d6413-0b78-41f0-8652-10d03fef6963
-- title:
--   Global Theory: det gram two frames
-- statement:
--   The Global Theory construction uses the det gram two frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetUpdateRowLastSingle.lean#L52-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetUpdateRowLastSingle.lean#L52-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.det_gram_two_frames {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (Matrix.fromBlocks (Matrix.diagonal fun i => if i = Fin.last r then -T else 0) Z W
      (Matrix.diagonal fun i => if i = Fin.last r then -T' else 0)).det
      = (-1) ^ (r + 1) * (Z.det * W.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det)) := by sorry
