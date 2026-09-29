-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isHomOnPoints_baseChange_comp
-- name    : GoodReductionJacobian.RelativeGroupLaw.isHomOnPoints_baseChange_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/60ad7c01-f36b-5337-a663-22ab8eb420ac
-- title:
--   Homomorphism on points is stable under affine base change
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} R$ a morphism, and let $L$ be a relative group law on $f$: a group structure, for every scheme $T$ and every $t : T \to \operatorname{Spec} R$, on the set of pairs $\langle \varphi, \varphi \circ f = t\rangle$ of morphisms $T \to A$ over $t$, given by operations `L.mul`, `L.one`, `L.inv` satisfying associativity, the unit laws, left inverses, and naturality in $T$ along morphisms compatible with the base morphisms. The assertion is: for all commutative rings $S'$, $S''$, every ring homomorphism $\psi : S' \to S''$, and all $s : \operatorname{Spec} S' \to \operatorname{Spec} R$, $s'' : \operatorname{Spec} S'' \to \operatorname{Spec} R$ with $s \circ \operatorname{Spec}\psi = s''$, given $\varphi : A \times_{\operatorname{Spec} R} \operatorname{Spec} S' \to A$ with $f \circ \varphi = s \circ \mathrm{pr}_2$ and $\varphi'' : A \times_{\operatorname{Spec} R} \operatorname{Spec} S'' \to A$ with $f \circ \varphi'' = s'' \circ \mathrm{pr}_2$, and assuming $\varphi'' = \varphi \circ G_\psi$ where $G_\psi = (\mathrm{pr}_1, \operatorname{Spec}\psi \circ \mathrm{pr}_2)$ is the base-change morphism, the following implication holds: if for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all $P, Q$ over $s \circ t'$ one has $\varphi \circ (P \cdot Q, t') = \varphi \circ (P,t') \cdot \varphi \circ (Q,t')$, where the products are taken by `L.mul` at the base morphism $s \circ t'$ and the pushed-forward sections are regarded as points over $s \circ t'$, then the same identity holds for $\varphi''$ with $t' : T \to \operatorname{Spec} S''$, points over $s'' \circ t'$, and products at $s'' \circ t'$.
--
--   This records that the property of being a homomorphism on points for a relative group law, stated as a clause about functorial points rather than as a named predicate, descends along affine base change $\operatorname{Spec} S'' \to \operatorname{Spec} S'$. It is used in the construction of the table scheme from a representing Hom-scheme, [`AlgebraicGeometry.exists_tableScheme_of_represents_homScheme`](thm.html#AlgebraicGeometry.exists_tableScheme_of_represents_homScheme), where homomorphism data over one base ring must be transported to a larger one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isHomOnPoints_baseChange_comp.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isHomOnPoints_baseChange_comp
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) :
    ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
      (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
      (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
      (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s)
      (φ'' : pullback f s'' ⟶ A) (hφ'' : φ'' ≫ f = pullback.snd f s'' ≫ s''),
      φ'' = pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ →
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
          (L.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S'')) (P Q : SchemeHomOver (t' ≫ s'') f),
        pullback.lift (L.mul (t' ≫ s'') P Q).1 t' (L.mul (t' ≫ s'') P Q).2 ≫ φ'' =
          (L.mul (t' ≫ s'')
            ⟨pullback.lift P.1 t' P.2 ≫ φ'', by rw [Category.assoc, hφ'', ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ'', by rw [Category.assoc, hφ'', ← Category.assoc, pullback.lift_snd]⟩).1) := by sorry
