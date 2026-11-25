-- Prove2me | Theorems.Thm_GlobalTheory_FibreAcyclic_exists_localRing
-- name    : GlobalTheory.FibreAcyclic.exists_localRing
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:03.96656+00:00
-- url     : https://prove2.me/theorems/1c63b448-35cf-5f3f-b15b-6bf52e02b1ab
-- title:
--   Fibre Acyclic: exists local Ring
-- statement:
--   The Fibre Acyclic construction uses the exists local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L263-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L263-L303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R] [IsLocalRing R]
omit [IsLocalRing R]
open AlgebraicGeometry

theorem GlobalTheory.FibreAcyclic.exists_localRing {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : ℕ) (hf : SmoothOfRelativeDimension g f) {K : Type} [Field K]
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : IsClosed {p (closedPoint K)}) (hc : f (p (closedPoint K)) = closedPoint A) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R) (_ : Algebra A R)
      (ξ : Spec (CommRingCat.of R) ⟶ X) (g₀ : R →+* K), Module.Flat A R ∧ IsPreimmersion ξ ∧
      ξ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A R)) ∧ IsLocalHom g₀ ∧
      Spec.map (CommRingCat.ofHom g₀) ≫ ξ = p ∧ IsRegularLocalRing (R ⧸ (maximalIdeal A).map (algebraMap A R)) ∧
      (g : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by sorry
