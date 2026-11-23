-- Prove2me | Theorems.Thm_GlobalTheory_coneExact_lTensor_of_quasiIso
-- name    : GlobalTheory.coneExact_lTensor_of_quasiIso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:10.910806+00:00
-- url     : https://prove2.me/theorems/b2e8eeec-4f94-40a5-9874-de658a7dc9a7
-- title:
--   Global Theory: cone Exact l Tensor of quasi Iso
-- statement:
--   The Global Theory construction uses the cone Exact l Tensor of quasi Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L471-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L471-L484

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
open Limits
variable {R : Type u} [CommRing R]

theorem GlobalTheory.coneExact_lTensor_of_quasiIso {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C)
    [hφ : QuasiIso φ] (hK : ∀ p, Module.Flat R (K.X p)) (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p))
    (M : Type*) [AddCommGroup M] [Module R M] :
    ConeExact (K := fun p => M ⊗[R] K.X p) (C := fun p => M ⊗[R] C.X p)
      (fun p => (K.d p (p + 1)).hom.lTensor M) (fun p => (C.d p (p + 1)).hom.lTensor M)
      (fun p => (φ.f p).hom.lTensor M) := by sorry
