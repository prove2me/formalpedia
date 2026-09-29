-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre
-- name    : GoodReductionJacobian.exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/ae69fb60-3c38-5188-9411-11bc8a7f6b95
-- title:
--   Relative group law over the completed local ring at s
-- statement:
--   Let $S$ be a Noetherian commutative ring (in universe $u$), let $Z$ be a scheme and $f : Z \to \operatorname{Spec} S$ a morphism which is smooth and proper, and suppose $f$ is projective in the explicit sense that there are $N \in \mathbb{N}$ and a closed immersion $\iota$ of $Z$ into $\operatorname{Proj}$ of the graded ring of homogeneous components of $S[x_0,\dots,x_N]$ such that $\iota$ followed by the structure morphism $\mathbb{P}^N_S \to \operatorname{Spec} S$ is $f$. Assume further that for every algebraically closed field $k$ and every ring homomorphism $x : S \to k$ the fibre product of $f$ with $\operatorname{Spec} x$ has connected underlying space. Let $\varepsilon$ be a section of $f$, i.e. a morphism $\operatorname{Spec} S \to Z$ composing with $f$ to the identity, and let $s$ be a point of $\operatorname{Spec} S$, with prime ideal $s.\mathrm{asIdeal}$. Assume that for every algebraically closed field $k$ and every ring homomorphism $x : S \to k$ with kernel exactly $s.\mathrm{asIdeal}$, the geometric fibre $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k \to \operatorname{Spec} k$ admits at least one relative group law, that is, a choice of multiplication, unit and inverse on the sets of $T$-points over $\operatorname{Spec} k$ for all $T$, satisfying associativity, the unit laws and the left inverse law, with multiplication natural in $T$. Write $\widehat{\mathcal O} =$ the adic completion of the local ring $\mathcal O_{S,s}$ (the localisation of $S$ at $s.\mathrm{asIdeal}$) along its maximal ideal. The conclusion is that the base change of $f$ along $\operatorname{Spec}$ of the composite $S \to \mathcal O_{S,s} \to \widehat{\mathcal O}$, viewed as a scheme over $\widehat{\mathcal O}$ via the second projection, carries a relative group law $L$ in the same sense, whose unit section at the identity of $\operatorname{Spec}\widehat{\mathcal O}$ is, as a morphism, the section obtained from $\varepsilon$ by base change, namely the morphism into the fibre product determined by $\operatorname{Spec}$ of that composite followed by $\varepsilon$ and by the identity.
--
--   This is the spreading-out step for good reduction: an abelian-variety structure on the geometric fibres over a single point $s$, together with a global section, produces a group law on the whole formal neighbourhood, i.e. over $\widehat{\mathcal O}_{S,s}$, normalised so that its unit is the given section. It is used to show that the locus of points of $\operatorname{Spec} S$ whose geometric fibres admit a relative group law is constrained, in [`GoodReductionJacobian.exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem`](thm.html#GoodReductionJacobian.exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicGeometry
open GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre
    {S : Type u} [CommRing S] [IsNoetherianRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (s : ↥(Spec (CommRingCat.of S)))
    (hs : (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k), RingHom.ker x = s.asIdeal →
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x)))))) :
    ∃ L : RelativeGroupLaw (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) (Localization.AtPrime s.asIdeal))
        (pullback.snd f (Spec.map (CommRingCat.ofHom
          ((algebraMap (Localization.AtPrime s.asIdeal)
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) (Localization.AtPrime s.asIdeal))).comp
            (algebraMap S (Localization.AtPrime s.asIdeal)))))),
      (L.one (𝟙 _)).1 =
        pullback.lift (Spec.map (CommRingCat.ofHom
          ((algebraMap (Localization.AtPrime s.asIdeal)
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) (Localization.AtPrime s.asIdeal))).comp
            (algebraMap S (Localization.AtPrime s.asIdeal)))) ≫ ε.1) (𝟙 _)
          (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp]) := by sorry
