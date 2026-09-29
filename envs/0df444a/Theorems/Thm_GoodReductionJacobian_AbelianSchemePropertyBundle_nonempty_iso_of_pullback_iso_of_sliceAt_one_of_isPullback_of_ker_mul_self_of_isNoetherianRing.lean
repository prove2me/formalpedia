-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/59fe4734-47cd-5620-ad8d-ba22ad6e051c
-- title:
--   Birigidified invertible modules on A× A over small extensions
-- statement:
--   Let $B_1$ be a commutative local noetherian ring with maximal ideal $\mathfrak m$, let $B_0$ be a commutative $B_1$-algebra whose structure map $B_1\to B_0$ is surjective, and let $K$ denote its kernel; assume $K\cdot K=0$ and $\mathfrak m\cdot K=0$. Let $f:A\to\operatorname{Spec}B_1$ be a morphism of schemes carrying a `RelativeGroupLaw` $L$ (a group structure, natural in the base change, on the sets of morphisms over a given $T\to\operatorname{Spec}B_1$) and satisfying `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper with connected fibres and admits some relative group law. Let $f_0:A_0\to\operatorname{Spec}B_0$ carry a relative group law $L_0$, and let $g:A_0\to A$ make the square over $\operatorname{Spec}B_0\to\operatorname{Spec}B_1$ cartesian and be compatible with the group laws, in the sense that for every $T\to\operatorname{Spec}B_0$ and all two sections $P,Q$ over it, composing $L_0$-multiplication with $g$ agrees with $L$-multiplication of $P\circ g$ and $Q\circ g$. Let $M,M'$ be invertible modules on $A\times_{\operatorname{Spec}B_1}A$ (each locally isomorphic to the unit) such that their pullbacks along the map $A_0\times_{\operatorname{Spec}B_0}A_0\to A\times_{\operatorname{Spec}B_1}A$ induced by $g$ on both factors are isomorphic, and such that each of $M$, $M'$ and each of their transports along the symmetry of $A\times_{\operatorname{Spec}B_1}A$ restricts to the unit module on the unit slice $\operatorname{sliceAt} f\,(L.\mathrm{one})$. Then $M$ and $M'$ are isomorphic.
--
--   This is the uniqueness statement in the deformation theory of birigidified invertible modules on the square $A\times A$ of an abelian scheme along a small square-zero extension of a local base: a birigidified module on $A\times_{B_1}A$ is determined by its restriction over $B_0$. It is used for the relative Picard functor of rigidified line bundles, and for the persistence of Rosati-compatibility for Mumford bundles on fake elliptic curves in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
    {B₁ B₀ : Type} [CommRing B₁] [IsLocalRing B₁] [IsNoetherianRing B₁] [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀))
    (hK : RingHom.ker (algebraMap B₁ B₀) * RingHom.ker (algebraMap B₁ B₀) = ⊥)
    (hKm : IsLocalRing.maximalIdeal B₁ * RingHom.ker (algebraMap B₁ B₀) = ⊥)
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B₁)}
    (L : RelativeGroupLaw B₁ f) (hA : AbelianSchemePropertyBundle B₁ f)
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)} (L₀ : RelativeGroupLaw B₀ f₀)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap B₁ B₀))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t' f₀),
      (L₀.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap B₁ B₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (M M' : (pullback f f).Modules) (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')

    (h0 : Nonempty
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj M ≅
        (Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj M'))

    (h1 : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj M ≅ 𝟙_ _))
    (h2 : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj M) ≅ 𝟙_ _))
    (h1' : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj M' ≅ 𝟙_ _))
    (h2' : Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B₁)))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj M') ≅ 𝟙_ _)) :
    Nonempty (M ≅ M') := by sorry
