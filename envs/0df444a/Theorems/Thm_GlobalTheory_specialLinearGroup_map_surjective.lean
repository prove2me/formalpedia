-- Prove2me | Theorems.Thm_GlobalTheory_specialLinearGroup_map_surjective
-- name    : GlobalTheory.specialLinearGroup_map_surjective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:51.05559+00:00
-- url     : https://prove2.me/theorems/cf42a04f-7252-4dcc-a510-3ee91dc5f992
-- title:
--   Global Theory: special Linear Group map surjective
-- statement:
--   The Global Theory construction uses the special Linear Group map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L178-L181

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
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem GlobalTheory.specialLinearGroup_map_surjective [Finite (MaximalSpectrum R)] (hf : Surjective f) :
    Surjective (SpecialLinearGroup.map (n := n) f) := by sorry
