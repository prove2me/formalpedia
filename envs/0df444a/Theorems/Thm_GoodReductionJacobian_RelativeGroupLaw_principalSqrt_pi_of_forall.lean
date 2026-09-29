-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_principalSqrt_pi_of_forall
-- name    : GoodReductionJacobian.RelativeGroupLaw.principalSqrt_pi_of_forall
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/37b73745-6b59-5cdf-82f8-01b5573e2599
-- title:
--   Principal square roots over a finite product of base rings
-- statement:
--   Let $S$ be a commutative ring, $f : A \to \operatorname{Spec} S$ a morphism of schemes, $L$ a relative group law on $f$ (a functorial group structure, natural in $T$, on the sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for each $t : T \to \operatorname{Spec} S$), and $\mathcal L$ a module on $A$ which is invertible, i.e. locally on $A$ its restriction is isomorphic to the unit. Let $k \in \mathbb N$ and let $C_0,\dots,C_{k-1}$ be commutative $S$-algebras. Assume for each $i$ the following holds over $C_i$: for every relative group law $L'$ on the base change $A \times_S \operatorname{Spec} C_i \to \operatorname{Spec} C_i$ which is compatible with $L$, in the sense that for all $T$, all $t' : T \to \operatorname{Spec} C_i$ and all sections $P, Q$ over $t'$ the morphism underlying $L'.\mathrm{mul}\,t'\,P\,Q$ followed by the first projection to $A$ coincides with the morphism underlying the $L$-product of $P$ and $Q$ composed with that projection, there exists an invertible module $\mathcal L_0$ on $A \times_S \operatorname{Spec} C_i$ such that (i) `KernelTrivial` holds for $L'$ and $\mathcal L_0$: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} C_i$ and every section $x$ over $t$, if the pullback along the slice morphism attached to $x$ of the Mumford bundle $m^*\mathcal L_0 \otimes p_1^*\mathcal L_0^\vee \otimes p_2^*\mathcal L_0^\vee$ becomes isomorphic to the unit after restriction over some open neighbourhood of each point of $\operatorname{Spec} R$, then $x$ is the identity section $L'.\mathrm{one}\,t$; and (ii) locally on the base, i.e. over some open neighbourhood of each point of $\operatorname{Spec} C_i$, the pullback of $\mathcal L$ along the projection $A \times_S \operatorname{Spec} C_i \to A$ is isomorphic to $\mathcal L_0 \otimes [-1]^*\mathcal L_0$, where $[-1]$ is the inversion morphism of $L'$ applied to the identity section. The conclusion is the same statement with $C_i$ replaced by the product ring $\prod_i C_i$, with its induced $S$-algebra structure.
--
--   This is the square-root clause in the definition of a canonical polarisation datum, asserted over a finite product of base rings: since $\operatorname{Spec} \prod_i C_i$ is the disjoint union of the $\operatorname{Spec} C_i$, the invertible square root and its kernel-triviality and local-isomorphism properties may be assembled componentwise. It is used in the construction of a faithfully flat base change over which a square root of a polarisation bundle exists, via [`CerednikDrinfeld.QM.IsCanonicalPolData.exists_faithfullyFlat_sqrt_of_forall_away_of_isInvertible`](thm.html#CerednikDrinfeld.QM.IsCanonicalPolData.exists_faithfullyFlat_sqrt_of_forall_away_of_isInvertible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_principalSqrt_pi_of_forall.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v

theorem GoodReductionJacobian.RelativeGroupLaw.principalSqrt_pi_of_forall
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra S (C i)]
    (hroot : ∀ i, (∀ (L' : RelativeGroupLaw (C i) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))),
          (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of (C i)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (C i))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) L')).obj 𝓛₀))) :
    (∀ (L' : RelativeGroupLaw (∀ i, C i) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))),
          (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of (∀ i, C i)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))) L')).obj 𝓛₀)) := by sorry
