-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_liftComp_baseChange_and_isHomOnPoints
-- name    : GoodReductionJacobian.RelativeGroupLaw.liftComp_baseChange_and_isHomOnPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/2bad3025-77a6-5736-81f4-9683d0cd53e8
-- title:
--   Base change and multiplicativity of the composite e_χ gg φ
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism equipped with a `RelativeGroupLaw` $L$, i.e. a multiplication, unit and inverse on the sets $\{\varphi : T \to A \mid \varphi \gg f = t\}$ of points of $A$ over each $t : T \to \operatorname{Spec} R$, satisfying associativity, the two unit laws, left inverses, and naturality under precomposition by morphisms $T' \to T$ over $\operatorname{Spec} R$. The assertion is a conjunction. First: for rings $S', S''$, a ring map $\psi : S' \to S''$, morphisms $s : \operatorname{Spec} S' \to \operatorname{Spec} R$ and $s'' : \operatorname{Spec} S'' \to \operatorname{Spec} R$ with $\operatorname{Spec}(\psi) \gg s = s''$, and morphisms $\varphi, \chi : A \times_R \operatorname{Spec} S' \to A$ over $s$ (that is, $\varphi \gg f = \mathrm{pr}_2 \gg s$ and likewise for $\chi$), write $G_\psi = (\mathrm{pr}_1, \mathrm{pr}_2 \gg \operatorname{Spec}(\psi)) : A \times_R \operatorname{Spec} S'' \to A \times_R \operatorname{Spec} S'$ and $e_\chi = (\chi, \mathrm{pr}_2)$; then $(G_\psi \gg \chi,\ \mathrm{pr}_2) \gg (G_\psi \gg \varphi) = G_\psi \gg (e_\chi \gg \varphi)$. Second: for a ring $S'$, $s : \operatorname{Spec} S' \to \operatorname{Spec} R$ and $\varphi, \chi$ as above, suppose each of $\varphi$ and $\chi$ is multiplicative on points, in the sense that for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all points $P, Q$ of $A$ over $t' \gg s$, the point $((P \cdot_L Q),\, t') \gg \varphi$ equals the $L$-product of $(P, t') \gg \varphi$ and $(Q, t') \gg \varphi$, and similarly for $\chi$; then any $\omega : A \times_R \operatorname{Spec} S' \to A$ over $s$ with $\omega = e_\chi \gg \varphi$ is multiplicative on points in the same sense.
--
--   The two clauses are the naturality in the base and the homomorphism property of the composition law on the functor of group endomorphisms of $A$ over $\operatorname{Spec} R$; they say that $\varphi \mapsto \varphi_*$ turns the composite $e_\chi \gg \varphi$ into $\varphi_* \circ \chi_*$, compatibly with affine base change. The result is used in [`AlgebraicGeometry.exists_tableScheme_of_represents_homScheme`](thm.html#AlgebraicGeometry.exists_tableScheme_of_represents_homScheme), where a representing scheme for the endomorphism functor is assembled and multiplication of endomorphisms must be matched with composition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_liftComp_baseChange_and_isHomOnPoints.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.liftComp_baseChange_and_isHomOnPoints
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) :
    (∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
        (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
        (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
        (φ χ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s) (hχ : χ ≫ f = pullback.snd f s ≫ s),
      pullback.lift (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ χ) (pullback.snd f s'')
          (by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs]) ≫
        (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ) =
      pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫
        (pullback.lift χ (pullback.snd f s) hχ ≫ φ)) ∧
    (∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ χ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s) (hχ : χ ≫ f = pullback.snd f s ≫ s),
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
          (L.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ χ =
          (L.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ (ω : pullback f s ⟶ A) (hω : ω ≫ f = pullback.snd f s ≫ s),
        ω = pullback.lift χ (pullback.snd f s) hχ ≫ φ →
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
          pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ ω =
            (L.mul (t' ≫ s)
              ⟨pullback.lift P.1 t' P.2 ≫ ω, by rw [Category.assoc, hω, ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ ω, by rw [Category.assoc, hω, ← Category.assoc, pullback.lift_snd]⟩).1)) := by sorry
