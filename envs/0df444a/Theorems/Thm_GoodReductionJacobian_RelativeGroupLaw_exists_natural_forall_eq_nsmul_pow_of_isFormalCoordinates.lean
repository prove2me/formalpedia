-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/30537a04-cb09-5c63-8389-c461478bbb75
-- title:
--   Katz's N^μ-trick on affine points of a smooth group law
-- statement:
--   Let $B$ and $B_0$ be commutative rings with $B_0$ a $B$-algebra such that $\operatorname{algebraMap} B B_0$ is surjective, let $\mu$ be a natural number with $I^{\mu+1}=0$ for $I=\ker(B\to B_0)$, and let $N$ be a natural number with $N=0$ in $B$. Let $f' \colon A' \to \operatorname{Spec} B$ be a smooth morphism of schemes equipped with a relative group law $L'$ (a group structure on the sections $\{\varphi : T \to A' \mid \varphi \circ f' = t\}$ for every $B$-scheme $t \colon T \to \operatorname{Spec} B$, natural in $T$) which is commutative, and suppose $L'$ has formal coordinates $\theta$ of dimension $d$ for a $d$-dimensional formal group law $F$ over $B$: for every $B$-algebra $B'$ the map $\theta$ sends tuples in $\mathrm{Fin}\,d \to B'$ to sections of $f'$ over $\operatorname{Spec} B'$, compatibly with $B$-algebra maps on nilpotent tuples, and for every ideal $J \subseteq B'$ with $J^{n+1}=0$ the tuples with entries in $J$ are carried bijectively onto the sections that reduce to the unit section modulo $J$, with $\theta(F.\mathrm{nilMul}\,n\,s\,t) = L'$-product of $\theta(s)$ and $\theta(t)$. Let further $f_Z \colon Z \to \operatorname{Spec} B$ and $f_{Z_0} \colon Z_0 \to \operatorname{Spec} B_0$ be given together with $g \colon Z_0 \to Z$ exhibiting $Z_0$ as the pull-back of $Z$ along $\operatorname{Spec} B_0 \to \operatorname{Spec} B$, and let $\psi \colon Z_0 \to A'$ satisfy $\psi$ followed by $f'$ equals $f_{Z_0}$ followed by $\operatorname{Spec}$ of $B \to B_0$. Then there is an assignment $\tilde N$ which, for every $B$-algebra $C$ and every $P \colon \operatorname{Spec} C \to Z$ with $P$ followed by $f_Z$ the structure morphism $\operatorname{Spec} C \to \operatorname{Spec} B$, produces a morphism $\tilde N_C(P) \colon \operatorname{Spec} C \to A'$ such that: (i) $\tilde N_C(P)$ followed by $f'$ is the structure morphism, so $\tilde N_C(P)$ is a $C$-point of $A'$ over $B$; (ii) for every $B$-algebra homomorphism $\varphi \colon C \to C'$ one has $\tilde N_{C'}(\operatorname{Spec}\varphi \text{ followed by } P) = \operatorname{Spec}\varphi$ followed by $\tilde N_C(P)$; and (iii) whenever $P_0 \colon \operatorname{Spec}(C/IC) \to Z_0$ satisfies $P_0$ followed by $g$ equals the reduction $\operatorname{Spec}(C/IC) \to \operatorname{Spec} C$ followed by $P$, and $x \colon \operatorname{Spec} C \to A'$ is a $C$-point of $A'$ over $B$ whose reduction modulo $IC$ equals $P_0$ followed by $\psi$, then $\tilde N_C(P)$ is the underlying morphism of the $N^{\mu}$-fold $L'$-multiple of $x$ over $\operatorname{Spec} C$.
--
--   This is the $N^{\mu}$-trick of Katz and Drinfeld in the form of a natural family of points: the $N^{\mu}$-multiple of an arbitrary lift of $\psi(P \bmod IC)$ depends only on $P$, because two lifts differ by a section infinitesimal along $IC$ and such sections are killed by $N^{\mu}$. It is the pointwise input to the construction of a morphism $Z \to A'$ lifting $N^{\mu}\psi$, used by [`GoodReductionJacobian.RelativeGroupLaw.exists_hom_lift_nsmul_pow_of_isFormalCoordinates`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_hom_lift_nsmul_pow_of_isFormalCoordinates) and, for fake elliptic curves, by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_lift_nsmul_pow`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_lift_nsmul_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates
    {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀))
    (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥) (N : ℕ) (hN : (N : B) = 0)

    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of B)} [Smooth f'] (L' : RelativeGroupLaw B f')
    (hc : L'.IsCommutative) {d : ℕ} (F : MvFormalGroup d B) (θ : RelativeGroupLaw.FormalCoordinates f' d)
    (hθ : L'.IsFormalCoordinates F θ)

    {Z Z₀ : Scheme.{0}} (fZ : Z ⟶ Spec (CommRingCat.of B)) (fZ₀ : Z₀ ⟶ Spec (CommRingCat.of B₀)) (g : Z₀ ⟶ Z)
    (hg : CategoryTheory.IsPullback g fZ₀ fZ (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (ψ : Z₀ ⟶ A') (hψ : ψ ≫ f' = fZ₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) :
    ∃ Ñ : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z),
        P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)) → (Spec (CommRingCat.of C) ⟶ A'),

      (∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
        (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))),
        Ñ C P hP ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B C))) ∧

      (∀ (C C' : Type) [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C'] (φ : C →ₐ[B] C')
        (P : Spec (CommRingCat.of C) ⟶ Z) (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (hP' : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P) ≫ fZ =
          Spec.map (CommRingCat.ofHom (algebraMap B C'))),
        Ñ C' (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P) hP' =
          Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Ñ C P hP) ∧

      (∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
        (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (P₀ : Spec (CommRingCat.of (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C))) ⟶ Z₀)
        (hP₀ : P₀ ≫ g =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ P)
        (x : Spec (CommRingCat.of C) ⟶ A') (hx : x ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (hlift : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ x =
          P₀ ≫ ψ),
        Ñ C P hP = (L'.nsmul (Spec.map (CommRingCat.ofHom (algebraMap B C))) (N ^ μ) ⟨x, hx⟩).1) := by sorry
