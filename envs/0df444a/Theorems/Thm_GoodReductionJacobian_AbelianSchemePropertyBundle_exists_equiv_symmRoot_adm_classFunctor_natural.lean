-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_equiv_symmRoot_adm_classFunctor_natural
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_equiv_symmRoot_adm_classFunctor_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/b3c447f8-46f0-5098-b9ed-bcae9ef8ae0b
-- title:
--   Given one symmetric root, root and admissible class functors agree
-- statement:
--   Let $R_0$ be a commutative ring, $A$ a scheme, $f\colon A\to\operatorname{Spec}R_0$ a morphism, $L$ a relative group law on $f$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec}R_0$, with the group axioms and compatibility with base change), and $hA$ the assertion that $f$ is smooth, proper, has connected fibres and admits a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible, i.e. locally trivial of rank one. Two hypotheses state that the relevant predicates on rigidified line bundles are stable under base change along morphisms $\varphi\colon B\to B'$ of $R_0$-algebras (objects of `Under (CommRingCat.of R₀)`): $h$ for `symmRootPred`, which says of $M$ on $A\times_{\operatorname{Spec}R_0}\operatorname{Spec}B$ that $M$ is symmetric for the base-changed group law and that the pullback of $\mathcal L$ is isomorphic to $M\otimes[-1]^{*}M$ locally over the base; $hadm$ for `admPred`, which says of $N$ that $[-1]^{*}N\cong N$ and $N\otimes N\cong\mathcal O$, both locally over the base. Let $W$ be an $R_0$-algebra and $M_0$ a line bundle on $A\times_{\operatorname{Spec}R_0}\operatorname{Spec}W$ rigidified along the unit section $L.\mathrm{one}$ and satisfying `symmRootPred`. Then there is a family of bijections $e_{B'}^{b}$, indexed by $R_0$-algebras $B'$ together with an $R_0$-algebra map $b\colon W\to B'$, from the set of isomorphism classes of rigidified line bundles satisfying `symmRootPred` over $B'$ to the set of isomorphism classes of rigidified line bundles satisfying `admPred` over $B'$ (the values at $B'$ of the two `classFunctor`s), such that for all $B'$, $B''$, all $b\colon W\to B'$, all $\psi\colon B'\to B''$ and all classes $x$ over $B'$ one has $e_{B''}^{b\psi}(\psi_{*}x)=\psi_{*}(e_{B'}^{b}x)$, where $\psi_{*}$ denotes the functorial base change.
--
--   This is the trivialisation statement for symmetric square roots (theta characteristics) of $\mathcal L$ on an abelian scheme: the functor of rigidified symmetric roots becomes, after the choice of one root over $W$, naturally identified with the functor of rigidified admissible bundles, classically a torsor identification under the dual of the $2$-torsion. It is used in the corepresentability statement [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_corepresents_symmRoot_classFunctor_under`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_corepresents_symmRoot_classFunctor_under), and rests on the two twisting lemmas saying that the quotient of two symmetric roots is admissible and that a symmetric root twisted by an admissible bundle is again a symmetric root.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_equiv_symmRoot_adm_classFunctor_natural.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_equiv_symmRoot_adm_classFunctor_natural
    {R₀ : Type} [CommRing R₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R₀ f) (hA : AbelianSchemePropertyBundle R₀ f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (hadm : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (SymmRoot.ψ R₀ R₀ φ)).L)
    (W : Type) [CommRing W] [Algebra R₀ W]
    (M₀ : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))))
    (h₀ : symmRootPred L 𝓛 R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) M₀.L) :
    ∃ e : ∀ (B' : Under (CommRingCat.of R₀)) (b : (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) ⟶ B'), (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B' ≃ (classFunctor f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm)).obj B',
      ∀ (B' B'' : Under (CommRingCat.of R₀)) (b : (Under.mk (CommRingCat.ofHom (algebraMap R₀ W))) ⟶ B') (ψ : B' ⟶ B'') (x : (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B'),
        e B'' (b ≫ ψ) ((classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map ψ x) = (classFunctor f (L.one (𝟙 _)) R₀ (admStablePred L R₀ hadm)).map ψ (e B' b x) := by sorry
