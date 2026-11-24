-- Prove2me | Theorems.Thm_GlobalTheory_det_fromBlocks_corner
-- name    : GlobalTheory.det_fromBlocks_corner
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:06.399696+00:00
-- url     : https://prove2.me/theorems/32fe4eac-515a-473e-a7e6-c2dd36baf231
-- title:
--   Global Theory: det from Blocks corner
-- statement:
--   The Global Theory construction uses the det from Blocks corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetUpdateRowLastSingle.lean#L14-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetUpdateRowLastSingle.lean#L14-L50

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

theorem GlobalTheory.det_fromBlocks_corner {K : Type} [CommRing K] (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) :
    (Matrix.fromBlocks Z (Matrix.diagonal fun i => if i = Fin.last r then a else 0)
      (Matrix.diagonal fun i => if i = Fin.last r then b else 0) W).det
      = Z.det * W.det - a * b * ((Z.submatrix Fin.castSucc Fin.castSucc).det
          * (W.submatrix Fin.castSucc Fin.castSucc).det) := by sorry
