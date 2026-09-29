-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen
-- name    : GoodReductionJacobian.exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/3c5f3002-ad54-5ecf-9ca0-55b01ae80e14
-- title:
--   Compatible group laws on all 𝔪-adic thickenings
-- statement:
--   Let $R$ be a noetherian commutative ring and let $f : A \to \operatorname{Spec} R$ be a morphism of schemes that is smooth and proper, admitting a closed immersion $\iota$ into $\operatorname{Proj}$ of the homogeneous subalgebra of $R[x_0,\dots,x_N]$ (projective $N$-space over $R$) with $\iota$ followed by the structure map `ProjSpace.π R N` equal to $f$, and let $e$ be a section of $f$, i.e. a morphism $\operatorname{Spec} R \to A$ composing with $f$ to the identity. Let $W \subseteq \operatorname{Spec} R$ be clopen such that for every $s \in W$ the fibre $f^{-1}(s)$ is connected, and such that for every algebraically closed field $k$ and every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} R$ with image contained in $W$ the base change $A \times_R \operatorname{Spec} k \to \operatorname{Spec} k$ satisfies `AbelianSchemePropertyBundle`: it is smooth, proper, has connected fibres, and carries a relative group law. Let $O'$ be a noetherian local ring with maximal ideal $\mathfrak m$ and $\varphi : R \to O'$ a ring homomorphism such that the image of the closed point of $\operatorname{Spec} O'$ under $\operatorname{Spec}\varphi$ lies in $W$. Write $A' := A \times_R \operatorname{Spec} O'$ and, for $n \in \mathbb N$, let $A'_n := A' \times_{O'} \operatorname{Spec}(O'/\mathfrak m^{n+1})$ be the $n$-th adic thickening, with its structure morphism `adicThickeningToBase` to $\operatorname{Spec}(O'/\mathfrak m^{n+1})$, its closed immersion `adicThickeningι` into $A'$, and its transition morphism `adicThickeningTransition` into $A'_{n+1}$. Then there exists a family $(L_n)_{n \in \mathbb N}$, where $L_n$ is a relative group law on $A'_n$ over $O'/\mathfrak m^{n+1}$ (a functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec}(O'/\mathfrak m^{n+1})$, satisfying associativity, the unit laws, left inverses and naturality of multiplication under base change), such that: (i) for every $n$, the unit section of $L_n$ at the identity of $\operatorname{Spec}(O'/\mathfrak m^{n+1})$, followed by the closed immersion $A'_n \to A'$, equals the projection $\operatorname{Spec}(O'/\mathfrak m^{n+1}) \to \operatorname{Spec} O'$ followed by the section of $A' \to \operatorname{Spec} O'$ induced by $e$ (the morphism into the pullback determined by $\operatorname{Spec}\varphi$ followed by $e$, and the identity); and (ii) every transition morphism is a homomorphism: for every $n$, every scheme $T$, every $t : T \to \operatorname{Spec}(O'/\mathfrak m^{n+1})$ and all $T$-points $P, Q$ of $A'_n$ over $t$, the product $L_n(P,Q)$ followed by $A'_n \to A'_{n+1}$ coincides with the underlying morphism of the product, formed with $L_{n+1}$ over the composite of $t$ with $\operatorname{Spec}$ of the quotient map $O'/\mathfrak m^{n+2} \to O'/\mathfrak m^{n+1}$, of $P$ and $Q$ each followed by that same transition.
--
--   This is the deformation tower step: starting from the group law on the residue fibre, which is an abelian variety because the closed point of $\operatorname{Spec} O'$ lies in the clopen locus $W$ of abelian geometric fibres, it produces group laws with unit induced by $e$ on all $\mathfrak m$-adic thickenings of $A \times_R \operatorname{Spec} O'$, compatible with the closed immersions $A'_n \hookrightarrow A'_{n+1}$. It is used to pass to the $\mathfrak m$-adic completion, in [`GoodReductionJacobian.exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_isNoetherianRing_of_isClopen`](thm.html#GoodReductionJacobian.exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_isNoetherianRing_of_isClopen), in the construction of the group law on the good-reduction model of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_AdicThickening

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen
    {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hs : Smooth f) (hp : IsProper f)
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (W : Set ↥(Spec (CommRingCat.of R))) (hW : IsClopen W)
    (hc : ∀ s : Spec (CommRingCat.of R), s ∈ W → _root_.IsConnected (f.base ⁻¹' {s}))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Set.range s.base ⊆ W → AbelianSchemePropertyBundle k (pullback.snd f s))
    (O' : Type u) [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O'] (φ : R →+* O')
    (hφ : (Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint O') ∈ W) :
    ∃ L : ∀ n : ℕ, RelativeGroupLaw (O' ⧸ IsLocalRing.maximalIdeal O' ^ (n + 1))
        (adicThickeningToBase (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n),
      (∀ n : ℕ, ((L n).one (𝟙 _)).1 ≫
          adicThickeningι (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n =
        adicThickeningBase (IsLocalRing.maximalIdeal O') n ≫
          pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ e.1) (𝟙 _)
            (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp])) ∧
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (O' ⧸ IsLocalRing.maximalIdeal O' ^ (n + 1))))
        (P Q : SchemeHomOver t (adicThickeningToBase (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n)),
        ((L n).mul t P Q).1 ≫ adicThickeningTransition (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n =
          ((L (n + 1)).mul (t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
              (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
                IsLocalRing.maximalIdeal O' ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal O' ^ (n + 1)))))
            ⟨P.1 ≫ adicThickeningTransition (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n, by
              rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ adicThickeningTransition (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n, by
              rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, Q.2]⟩).1) := by sorry
