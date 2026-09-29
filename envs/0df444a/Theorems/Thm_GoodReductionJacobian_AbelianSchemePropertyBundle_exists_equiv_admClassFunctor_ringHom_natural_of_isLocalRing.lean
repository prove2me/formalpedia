-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_equiv_admClassFunctor_ringHom_natural_of_isLocalRing
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_equiv_admClassFunctor_ringHom_natural_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/a8bc502a-f223-5daa-93d8-9eeb32575b3c
-- title:
--   Local corepresentability of admissible rigidified bundle classes
-- statement:
--   Let $R_0$ be a noetherian local commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}R_0$ a morphism (everything in the bottom universe), let $L$ be a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi\colon T\to A\mid \varphi\circ f=t\}$ of $T$-points over $\operatorname{Spec}R_0$, compatible with base change, and assume `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Assume further that the predicate $\mathrm{admPred}$ is stable under base change: whenever $\varphi\colon B\to B'$ is a morphism of $R_0$-algebras and $N$ is a line bundle on $A\times_{\operatorname{Spec}R_0}\operatorname{Spec}B$ rigidified along the unit section of $L$ such that, locally over the base $\operatorname{Spec}B$, the pullback of $N$ along the inversion morphism of the base-changed group law is isomorphic to $N$ and $N\otimes N$ is isomorphic to the unit module, then the same two local conditions hold for the pullback of $N$ along $\varphi$. The conclusion asserts the existence of a commutative ring $D$ with an $R_0$-algebra structure making it a finite free $R_0$-module, nontrivial, together with bijections, for every $R_0$-algebra $B'$, between the set of isomorphism classes of rigidified line bundles on $A\times_{\operatorname{Spec}R_0}\operatorname{Spec}B'$ satisfying those two local conditions (the value at $B'$ of `classFunctor` for the stable predicate built from $\mathrm{admPred}$ and the above stability) and the set of ring homomorphisms $D\to B'$ whose composite with $R_0\to D$ is the structure map of $B'$; and these bijections are natural: for $\psi\colon B'\to B''$ and any class $x$ over $B'$, the homomorphism attached to the pullback of $x$ along $\psi$ is $\psi$ composed after the homomorphism attached to $x$.
--
--   This is the local (noetherian local base) corepresentability statement for the functor of admissible, i.e. symmetric and square-trivial, rigidified line bundles on an abelian scheme: the corepresenting algebra $D$ is the affine algebra of the Cartier dual of the $2$-torsion subgroup scheme. It is the input to the globalisation step [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_corepresents_symmRoot_classFunctor_under`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_corepresents_symmRoot_classFunctor_under), on the way to constructing symmetric square roots used in the Jacobian good-reduction input to level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_equiv_admClassFunctor_ringHom_natural_of_isLocalRing.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SymmRootFunctor
import Definitions.Def_AlgebraicGeometry_SymmRootAdm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.SymmRoot

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_equiv_admClassFunctor_ringHom_natural_of_isLocalRing
    {R₀ : Type} [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra R₀ D) (_ : Module.Finite R₀ D) (_ : Module.Free R₀ D) (_ : Nontrivial D),
      ∃ e : ∀ B' : Under (CommRingCat.of R₀),
          (classFunctor f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm)).obj B' ≃
            {φ : D →+* B'.right // φ.comp (algebraMap R₀ D) = B'.hom.hom},
        ∀ (B' B'' : Under (CommRingCat.of R₀)) (ψ : B' ⟶ B'')
          (x : (classFunctor f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm)).obj B'),
          ((e B'') ((classFunctor f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm)).map ψ x)).1 =
            ψ.right.hom.comp ((e B') x).1 := by sorry
