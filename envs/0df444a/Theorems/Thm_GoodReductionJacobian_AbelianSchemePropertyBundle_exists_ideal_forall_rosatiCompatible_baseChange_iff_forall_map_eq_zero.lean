-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_ideal_forall_rosatiCompatible_baseChange_iff_forall_map_eq_zero
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_ideal_forall_rosatiCompatible_baseChange_iff_forall_map_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/ba40ed80-f26c-5383-b51e-f6c55251479c
-- title:
--   Ideal-theoretic representability of the Rosati-compatibility locus
-- statement:
--   Let $S$ be a noetherian commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, equipped with a relative group law $L$ (functorial group structure on $S$-points, with multiplication natural in the test scheme) and with the data $hA$ recording that $f$ is smooth, proper, has connected fibres and admits a relative group law. Let $\mathcal{L}$ be a module on $A$ that is invertible, in the sense that every point of $A$ has an open neighbourhood on which the restriction of $\mathcal{L}$ is isomorphic to the unit module; let $I$ be a type, $act : I \to \operatorname{End}(A)$ a family of endomorphisms each satisfying $act_x$ followed by $f$ equals $f$, and $star : I \to I$ an involution-like map. Then there is a family of ideals $J_b \subseteq S$, $b \in I$, with the following property: for every commutative $S$-algebra $R$, writing $A_R$ for the fibre product of $f$ with $\operatorname{Spec}$ of the structure map, for every relative group law $L'$ on $A_R$ over $R$ whose multiplication is compatible with $L$ under the first projection (for all test data $t'$ and sections $P,Q$, the projection of $L'.\mathrm{mul}\,t'\,P\,Q$ is the projection of the $L$-product of the projected sections), and for every family $act' : I \to \operatorname{End}(A_R)$ over $\operatorname{Spec} R$ with $act'_x$ followed by the first projection equal to the first projection followed by $act_x$, the predicate `RosatiCompatible` for $A_R \to \operatorname{Spec} R$, $L'$, the pullback of $\mathcal{L}$ to $A_R$, $act'$ and $star$ — i.e. for each $b \in I$ the pullbacks of the Mumford bundle $m^{*}\mathcal{M} \otimes (p_1^{*}\mathcal{M}^{\vee} \otimes p_2^{*}\mathcal{M}^{\vee})$ along $(\mathrm{id}, act'_b)$ and along $(act'_{star(b)}, \mathrm{id})$ on $A_R \times_{\operatorname{Spec} R} A_R$ are isomorphic over some open neighbourhood of each point of the base — holds if and only if every element of every $J_b$ maps to $0$ in $R$. Note that the right-hand side of the equivalence is the simultaneous vanishing of the images of all the ideals $J_b$, and that one family $(J_b)_b$ works for all $R$, $L'$ and $act'$ at once.
--
--   This is the representability of the Rosati-compatibility locus of a line bundle on an abelian scheme with respect to a family of endomorphisms: the locus is cut out on the base by a family of ideals, functorially in the base change. It is used by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_rosatiCompatible_away_of_rosatiCompatible_atPrime_of_isNoetherianRing`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_rosatiCompatible_away_of_rosatiCompatible_atPrime_of_isNoetherianRing) to spread Rosati compatibility from a local statement at a prime to a neighbourhood.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_ideal_forall_rosatiCompatible_baseChange_iff_forall_map_eq_zero.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_ideal_forall_rosatiCompatible_baseChange_iff_forall_map_eq_zero
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I) :
    ∃ J : I → Ideal S, ∀ (R : Type) [CommRing R] [Algebra S R],
      (∀ (L' : RelativeGroupLaw (R) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (R)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (R))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∀ (act' : I → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))) ⟶
              pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (R))))))
            (act'_over : ∀ x : I, act' x ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))) =
              pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (R))))),
            (∀ x : I, act' x ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))) =
              pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))) ≫ act x) →
          (RosatiCompatible (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (R))))) L'
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (R)))))).obj 𝓛)
            act' act'_over star ↔
            ∀ b : I, ∀ x ∈ J b, algebraMap S (R) x = 0)) := by sorry
