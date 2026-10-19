-- Prove2me | Theorems.Thm_MazurTransfer_ProperGenericInertiaFibres_generic_inertia_fixed_of_image_fixed
-- name    : MazurTransfer.ProperGenericInertiaFibres.generic_inertia_fixed_of_image_fixed
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T04:46:00.662363+00:00
-- url     : https://prove2.me/theorems/6bf5259d-b775-4143-a5e2-8c79425d8938
-- title:
--   Inertia-fixed lifts after field base change of a proper unramified map
-- statement:
--   Let $R$ be a commutative ring, $K$ a field over $R$, and $\Omega$ a field with compatible $K$- and $R$-algebra structures. Let $J$ be proper over $R$ and let $\phi:J\to J$ be an endomorphism over $R$, formally unramified and locally of finite type. Write $J_K$ and $\phi_K$ for their base changes to $K$. Let $A$ be a valuation subring of $\Omega$ containing the image of $R$, and let $\sigma$ lie in its inertia subgroup inside $\operatorname{Aut}_K(\Omega)$.
--
--   For an $\Omega$-point $x$ of $J_K$,
--
--   $$\sigma(\phi_K(x))=\phi_K(x)\quad\Longrightarrow\quad\sigma(x)=x.$$
--
--   This transfers proper unramified lift uniqueness to the field base change used for actual local norm fibres. No fraction-field, Galois, algebraic-closedness or characteristic-zero hypothesis is added.
-- source:
--   MazurTheorem, ProperGenericInertiaFibres.lean, complete original theorem and hypotheses, full source SHA-256 e18b9d1fd9bf12615a4eb07b924372e9db8aca66d791a45a1e4b924906562ee3, Apache-2.0. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transfer proper unramified inertia lift uniqueness to
the generic fibre, retaining the actual scalar and Galois maps.
Named downstream consumer: good-prime inertia fixed rational norm lifts.
-/
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_MazurTransfer_ProperUnramifiedInertiaFibres_inertia_fixed_of_image_fixed

noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u

theorem MazurTransfer.ProperGenericInertiaFibres.generic_inertia_fixed_of_image_fixed
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (φ : SchemeHomOver f f) [FormallyUnramified φ.val] [LocallyOfFiniteType φ.val]
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap R Ω r ∈ A)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ A.inertiaSubgroupIn K)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (hx : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val ≫
      (genericFibreRestrict R K f f φ).val =
      x.val ≫ (genericFibreRestrict R K f f φ).val) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val := by sorry
