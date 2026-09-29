-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_symmRoot_classFunctor_injective_and_exists_of_flat_of_surjective_typeZero
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.symmRoot_classFunctor_injective_and_exists_of_flat_of_surjective_typeZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/614a8b76-e095-5d7f-8a5e-92dec3369a17
-- title:
--   Flat descent for the symmetric square root class functor
-- statement:
--   Let $S$ be a commutative ring, $f\colon A\to\operatorname{Spec} S$ a morphism of schemes (in universe $0$), $L$ a relative group law on $f$ (a functorial group structure on the sets of $\operatorname{Spec}S$-morphisms into $A$, compatible with base change), and let $hA$ assert that $f$ is smooth and proper with connected fibres and admits a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible, i.e. locally isomorphic to the unit module, and let $R_0$ be an $S$-algebra. The hypothesis $h$ states that the predicate $\mathtt{symmRootPred}$ is stable under base change: for every morphism $\varphi\colon B\to B'$ of $R_0$-algebras (objects of $\mathtt{Under}\,R_0$) and every line bundle $M$ on $A\times_S\operatorname{Spec}B$ rigidified along the unit section $L.\mathtt{one}$, if $M$ satisfies $\mathtt{symmRootPred}$ then so does its pullback along $\varphi$. Here $\mathtt{symmRootPred}$ for a module $M$ on $A\times_S\operatorname{Spec}B$ says that $M$ is symmetric for the base-changed group law, i.e. its pullback along the inversion morphism is isomorphic to $M$ locally over $\operatorname{Spec}B$, and that the pullback of $\mathcal L$ to $A\times_S\operatorname{Spec}B$ is, again locally over $\operatorname{Spec}B$, isomorphic to the tensor product of $M$ with its pullback along inversion. Write $F$ for the associated class functor `classFunctor`, which sends an $R_0$-algebra $B$ to the set of such rigidified bundles on $A\times_S\operatorname{Spec}B$ satisfying $\mathtt{symmRootPred}$, taken modulo isomorphism, and a morphism to pullback of classes. Then for all $R_0$-algebras $B,B'$ and every morphism $\varphi\colon B\to B'$ whose underlying ring map is flat and induces a surjection on prime spectra, the map $F(\varphi)$ is injective, and every class $y\in F(B')$ whose two images under the maps induced by the two canonical morphisms $B'\to B'\otimes_B B'$ (the pushout inclusions of $\varphi$ with itself) coincide is of the form $F(\varphi)(x)$ for some $x\in F(B)$.
--
--   This is the fpqc sheaf condition — injectivity together with effective descent for flat surjective base change — for the functor of isomorphism classes of rigidified symmetric square roots of $\mathcal L$ on an abelian scheme, stated in the equaliser shape required by the representability criterion. It is used in the construction of finite faithfully flat covers realising such square roots locally at a prime, en route to the polarisation data for the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_symmRoot_classFunctor_injective_and_exists_of_flat_of_surjective_typeZero.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SymmRootFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.SymmRoot

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.symmRoot_classFunctor_injective_and_exists_of_flat_of_surjective_typeZero
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R₀ : Type) [CommRing R₀] [Algebra S R₀]
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι S R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ S R₀ φ)).L)
    (B B' : Under (CommRingCat.of R₀)) (φ : B ⟶ B')
    (hflat : φ.right.hom.Flat) (hsurj : Function.Surjective (PrimeSpectrum.comap φ.right.hom)) :
    Function.Injective ((classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map φ) ∧
      ∀ y : (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B',
        (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map (pushout.inl φ φ) y =
          (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map (pushout.inr φ φ) y →
        ∃ x : (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B,
          (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map φ x = y := by sorry
