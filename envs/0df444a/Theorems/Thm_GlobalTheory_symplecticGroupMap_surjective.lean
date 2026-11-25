-- Prove2me | Theorems.Thm_GlobalTheory_symplecticGroupMap_surjective
-- name    : GlobalTheory.symplecticGroupMap_surjective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:07.543827+00:00
-- url     : https://prove2.me/theorems/ee17d0e2-9b1a-4735-818d-638a046573ee
-- title:
--   Global Theory: symplectic Group Map surjective
-- statement:
--   The Global Theory construction uses the symplectic Group Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L343-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L343-L346

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
  {l : Type*} [Fintype l] [DecidableEq l]

theorem GlobalTheory.symplecticGroupMap_surjective [Finite (MaximalSpectrum R)] (hf : Surjective f) :
    Surjective (symplecticGroupMap l f) := by sorry
