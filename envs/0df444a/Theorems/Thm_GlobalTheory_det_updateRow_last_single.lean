-- Prove2me | Theorems.Thm_GlobalTheory_det_updateRow_last_single
-- name    : GlobalTheory.det_updateRow_last_single
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:15:57.99682+00:00
-- url     : https://prove2.me/theorems/b482e38d-dc3e-4e75-89dd-3a8f0e9a492f
-- title:
--   Global Theory: det update Row last single
-- statement:
--   The Global Theory construction uses the det update Row last single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetUpdateRowLastSingle.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetUpdateRowLastSingle.lean#L7-L12

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

theorem GlobalTheory.det_updateRow_last_single {K : Type} [CommRing K] (r : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (Z.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det
      = (Z.submatrix Fin.castSucc Fin.castSucc).det := by sorry
