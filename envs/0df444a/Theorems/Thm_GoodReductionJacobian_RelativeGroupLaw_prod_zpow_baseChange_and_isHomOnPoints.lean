-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_prod_zpow_baseChange_and_isHomOnPoints
-- name    : GoodReductionJacobian.RelativeGroupLaw.prod_zpow_baseChange_and_isHomOnPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/324ed794-ee82-5e3e-864e-bd9ae30dd482
-- title:
--   Base change and homomorphy of monomials prod_l φ_l^{e_l}
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism, and let $L$ be a relative group law on $f$ in the sense of `RelativeGroupLaw`: a group structure `L.mul`, `L.one`, `L.inv` on each set $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-valued points over a base morphism $t : T \to \operatorname{Spec} R$, satisfying the group axioms and naturality of `mul` under precomposition with any $\psi : T' \to T$ over $\operatorname{Spec} R$. Assume `L.IsCommutative`, i.e. `L.mul t x y = L.mul t y x` always; then each point set carries the commutative group structure `L.pointCommGroup hc t`. Fix $n \in \mathbb{N}$ and $e : \mathrm{Fin}\,n \to \mathbb{Z}$. Two assertions are made together. First: for commutative rings $S', S''$, a ring homomorphism $\psi : S' \to S''$, morphisms $s : \operatorname{Spec} S' \to \operatorname{Spec} R$ and $s'' : \operatorname{Spec} S'' \to \operatorname{Spec} R$ with $\operatorname{Spec}\psi$ followed by $s$ equal to $s''$, and a family $\varphi : \mathrm{Fin}\,n \to (A \times_R \operatorname{Spec} S' \to A)$ with each $\varphi_l$ followed by $f$ equal to $\mathrm{pr}_2$ followed by $s$, write $G_\psi = (\mathrm{pr}_1, \mathrm{pr}_2 \text{ followed by } \operatorname{Spec}\psi) : A \times_R \operatorname{Spec} S'' \to A \times_R \operatorname{Spec} S'$; then the underlying morphism of $\prod_l (G_\psi \text{ followed by } \varphi_l)^{e_l}$, computed in the commutative group of points over $\mathrm{pr}_2$ followed by $s''$, equals $G_\psi$ followed by the underlying morphism of $\prod_l \varphi_l^{e_l}$, computed over $\mathrm{pr}_2$ followed by $s$. Second: for a commutative ring $S'$, $s : \operatorname{Spec} S' \to \operatorname{Spec} R$ and $\varphi$ as above, if every $\varphi_l$ is multiplicative on points — for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all $P, Q$ over $t'$ followed by $s$, the lift of $L.\mathrm{mul}\,P\,Q$ along $t'$ followed by $\varphi_l$ equals $L.\mathrm{mul}$ of the images of $P$ and $Q$ under $\varphi_l$ — then any $\omega : A \times_R \operatorname{Spec} S' \to A$ over $s$ whose underlying morphism is that of $\prod_l \varphi_l^{e_l}$ satisfies the same multiplicativity condition on points.
--
--   This records that integral monomials in the group of relative points behave as expected: they are compatible with affine base change along $\operatorname{Spec}\psi$, and the property of inducing a homomorphism on $T$-valued points is inherited by monomials of such morphisms. It is used in the construction of the auxiliary scheme in [`AlgebraicGeometry.exists_tableScheme_of_represents_homScheme`](thm.html#AlgebraicGeometry.exists_tableScheme_of_represents_homScheme), where monomials of endomorphism-valued points of a group scheme with good reduction must be seen to be endomorphisms again.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_prod_zpow_baseChange_and_isHomOnPoints.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.prod_zpow_baseChange_and_isHomOnPoints
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ) (e : Fin n → ℤ) :
    (∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
        (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
        (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
        (φ : Fin n → (pullback f s ⟶ A)) (hφ : ∀ l, φ l ≫ f = pullback.snd f s ≫ s),
      (letI := L.pointCommGroup hc (pullback.snd f s'' ≫ s'');
          (∏ l, (⟨pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ l, by rw [Category.assoc, hφ l, ← Category.assoc, pullback.lift_snd, Category.assoc, hs]⟩ : SchemeHomOver (pullback.snd f s'' ≫ s'') f) ^ (e l))).1 =
        pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫
          (letI := L.pointCommGroup hc (pullback.snd f s ≫ s);
          (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (e l))).1) ∧
    (∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : Fin n → (pullback f s ⟶ A)) (hφ : ∀ l, φ l ≫ f = pullback.snd f s ≫ s),
      (∀ l, (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
          pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ l =
            (L.mul (t' ≫ s)
              ⟨pullback.lift P.1 t' P.2 ≫ φ l, by rw [Category.assoc, hφ l, ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ φ l, by rw [Category.assoc, hφ l, ← Category.assoc, pullback.lift_snd]⟩).1)) →
      ∀ (ω : pullback f s ⟶ A) (hω : ω ≫ f = pullback.snd f s ≫ s),
        ω = (letI := L.pointCommGroup hc (pullback.snd f s ≫ s);
          (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (e l))).1 →
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
          pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ ω =
            (L.mul (t' ≫ s)
              ⟨pullback.lift P.1 t' P.2 ≫ ω, by rw [Category.assoc, hω, ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ ω, by rw [Category.assoc, hω, ← Category.assoc, pullback.lift_snd]⟩).1)) := by sorry
