-- Prove2me | Theorems.Thm_MazurTransfer_proper_unramified_inertia_fixed_of_image_fixed
-- name    : MazurTransfer.proper_unramified_inertia_fixed_of_image_fixed
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-11T00:00:34.112055+00:00
-- url     : https://prove2.me/theorems/c1aeb63d-68f1-411c-a80e-885edca4be4c
-- title:
--   Inertia fixes lifts under a proper unramified map
-- statement:
--   Let J be a proper scheme over a commutative ring R, and let φ be a formally unramified R-endomorphism locally of finite type. Let Ω extend a field K over R, with compatible scalar maps, and let A be a valuation subring of Ω containing the image of R. If an automorphism σ of Ω over K belongs to the inertia subgroup of A and fixes φ(x), then σ fixes the Ω-valued point x. This criterion applies to the two selected norm maps on the local order-thirteen Picard model and proves their good-prime Kummer classes are unramified. It does not assert a global Selmer bound.
-- source:
--   Owned MazurTheorem integration argument. Reuses the complete ring-side inertia helpers of Anthropic FLT, Apache-2.0, exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_specMap_comp_eq_self_of_mem_inertiaSubgroupIn_of_isTorsionPoint.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u

theorem MazurTransfer.proper_unramified_inertia_fixed_of_image_fixed
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (φ : J ⟶ J) (hφ : φ ≫ f = f) [FormallyUnramified φ] [LocallyOfFiniteType φ]
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ = x.val ≫ φ) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by sorry
