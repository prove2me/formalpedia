-- Prove2me | Theorems.Thm_GlobalTheory_tensor_quot_maximalIdeal_finite_formallyUnramified
-- name    : GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:32.879507+00:00
-- url     : https://prove2.me/theorems/80d91a51-5f90-4e87-bbfd-868907b84d4d
-- title:
--   Global Theory: tensor quot maximal Ideal finite formally Unramified
-- statement:
--   The Global Theory construction uses the tensor quot maximal Ideal finite formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TensorResidueUnramifiedFinite.lean#L6-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TensorResidueUnramifiedFinite.lean#L6-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorResidueUnramifiedFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified :
    ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R] [Algebra A B]
      [Algebra A R], ((IsLocalRing.residue R).comp (algebraMap A R)).Finite →
      ((IsLocalRing.residue R).comp (algebraMap A R)).FormallyUnramified →
      Algebra.FormallyUnramified B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) ∧
      Module.Finite B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) := by sorry
