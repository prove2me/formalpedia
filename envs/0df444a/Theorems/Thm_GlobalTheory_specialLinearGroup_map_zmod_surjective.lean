-- Prove2me | Theorems.Thm_GlobalTheory_specialLinearGroup_map_zmod_surjective
-- name    : GlobalTheory.specialLinearGroup_map_zmod_surjective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:58.967425+00:00
-- url     : https://prove2.me/theorems/51c02d99-d1df-5f7c-8d8c-92554ac3ae5f
-- title:
--   Global Theory: special Linear Group map zmod surjective
-- statement:
--   The Global Theory construction uses the special Linear Group map zmod surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L636-L641
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L636-L641

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
open TensorProduct

theorem GlobalTheory.specialLinearGroup_map_zmod_surjective (n : Type*) [Fintype n] [DecidableEq n] (N : ℕ) :
    Surjective (SpecialLinearGroup.map (n := n) (Int.castRingHom (ZMod N))) := by sorry
