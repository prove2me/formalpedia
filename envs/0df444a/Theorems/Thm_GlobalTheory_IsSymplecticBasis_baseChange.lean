-- Prove2me | Theorems.Thm_GlobalTheory_IsSymplecticBasis_baseChange
-- name    : GlobalTheory.IsSymplecticBasis.baseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:45.635599+00:00
-- url     : https://prove2.me/theorems/5789aa82-fe66-4089-a5bf-4638b3cd9571
-- title:
--   Is Symplectic Basis: base Change
-- statement:
--   The Is Symplectic Basis construction uses the base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L587-L593
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L587-L593

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
variable {S R Λ l : Type*} [CommRing S] [CommRing R] [AddCommGroup Λ] [Module S Λ] [Fintype l]
  {B : LinearMap.BilinForm S Λ}
omit [Fintype l]

theorem GlobalTheory.IsSymplecticBasis.baseChange [Algebra S R] {b : Basis (l ⊕ l) S Λ}
    (hb : IsSymplecticBasis B b) : IsSymplecticBasis (B.baseChange R) (b.baseChange R) := by sorry
