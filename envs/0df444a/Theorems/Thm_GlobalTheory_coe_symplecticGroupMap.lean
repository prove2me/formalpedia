-- Prove2me | Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
-- name    : GlobalTheory.coe_symplecticGroupMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:12:30.825931+00:00
-- url     : https://prove2.me/theorems/f380b937-a9fb-4371-a09e-c60a11bcc040
-- title:
--   Global Theory: coe symplectic Group Map
-- statement:
--   The Global Theory construction uses the coe symplectic Group Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L197-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L197-L198

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

theorem GlobalTheory.coe_symplecticGroupMap (A : symplecticGroup l S) :
    (symplecticGroupMap l f A).1 = A.1.map f := by sorry

attribute [defeq] GlobalTheory.coe_symplecticGroupMap
