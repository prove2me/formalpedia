-- Prove2me | Theorems.Thm_GlobalTheory_ConjLocal_exists_isUnit_det_iterMat
-- name    : GlobalTheory.ConjLocal.exists_isUnit_det_iterMat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:25:36.549007+00:00
-- url     : https://prove2.me/theorems/444c828d-df87-434a-be03-85286fa98e52
-- title:
--   Conj Local: exists is Unit det iter Mat
-- statement:
--   The Conj Local construction uses the exists is Unit det iter Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentIterates.lean#L83-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLinearIndependentIterates.lean#L83-L104

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentIterates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.ConjLocal
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.ConjLocal.exists_isUnit_det_iterMat [IsLocalRing R] (Y : Matrix (Fin n) (Fin n) R) (hs : Y.charpoly.Separable) :
    ∃ v : Fin n → R, IsUnit (iterMat Y v).det := by sorry
