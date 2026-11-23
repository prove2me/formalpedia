-- Prove2me | Theorems.Thm_GlobalTheory_isUnit_of_forall_maximalSpectrum_mk_ne_zero
-- name    : GlobalTheory.isUnit_of_forall_maximalSpectrum_mk_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:12:15.76962+00:00
-- url     : https://prove2.me/theorems/7cd1e08e-3bce-4a42-8499-6eaa6b061c09
-- title:
--   Global Theory: is Unit of forall maximal Spectrum mk ne zero
-- statement:
--   The Global Theory construction uses the is Unit of forall maximal Spectrum mk ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L15-L19

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
variable {R : Type*} [CommRing R]

theorem GlobalTheory.isUnit_of_forall_maximalSpectrum_mk_ne_zero {x : R}
    (h : ∀ m : MaximalSpectrum R, Ideal.Quotient.mk m.asIdeal x ≠ 0) : IsUnit x := by sorry
