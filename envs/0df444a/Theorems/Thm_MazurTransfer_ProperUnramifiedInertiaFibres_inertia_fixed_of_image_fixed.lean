-- Prove2me | Theorems.Thm_MazurTransfer_ProperUnramifiedInertiaFibres_inertia_fixed_of_image_fixed
-- name    : MazurTransfer.ProperUnramifiedInertiaFibres.inertia_fixed_of_image_fixed
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T04:32:36.088494+00:00
-- url     : https://prove2.me/theorems/14bd37ef-e97b-47d9-bb5b-64bf7a8db3b3
-- title:
--   Inertia fixes a lift under a proper unramified relative endomorphism
-- statement:
--   Let $R$ be a commutative ring, $K$ a field over $R$, and $\Omega$ an extension field with compatible $R$- and $K$-algebra structures. Let $J$ be proper over $\operatorname{Spec}R$, and let $\phi:J\to J$ be an endomorphism over $R$ that is formally unramified and locally of finite type. Let $A$ be a valuation subring of $\Omega$ containing the image of $R$.
--
--   For $\sigma$ in the inertia subgroup attached to $A$ inside $\operatorname{Aut}_K(\Omega)$ and an $\Omega$-point $x$ of $J$,
--
--   $$\sigma(\phi(x))=\phi(x)\quad\Longrightarrow\quad\sigma(x)=x.$$
--
--   This general statement supplies inertia-fixed norm lifts once the actual local integral norm map is proved finite étale. No Galois, algebraic-closedness or characteristic-zero assumption is added.
-- source:
--   MazurTheorem, ProperUnramifiedInertiaFibres.lean, complete original theorem and hypotheses, source SHA-256 0864c3f8432def3d1f1205dc0ed70a14809907edc4267f667a8ab9ccc712eb9a, Apache-2.0. Official Anthropic FLT at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inertia fixes a geometric point of a proper relative
scheme whenever a formally unramified relative endomorphism has an
inertia fixed image. Uses the valuation-subring decomposition and inertia
groups and lift uniqueness from exact-pin Anthropic FLT.
Named downstream consumer: good-prime Kummer lifts for the SAME selected
integral order-13 norm maps.
-/
import Definitions.Def_MazurTransfer_ValuationSubringInertiaRingData
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified

noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open MazurTransfer.ValuationSubringInertiaRingData
universe u

theorem MazurTransfer.ProperUnramifiedInertiaFibres.inertia_fixed_of_image_fixed
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (φ : J ⟶ J) (hφ : φ ≫ f = f) [FormallyUnramified φ] [LocallyOfFiniteType φ]
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f)
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫ φ = x.val ≫ φ) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by sorry
