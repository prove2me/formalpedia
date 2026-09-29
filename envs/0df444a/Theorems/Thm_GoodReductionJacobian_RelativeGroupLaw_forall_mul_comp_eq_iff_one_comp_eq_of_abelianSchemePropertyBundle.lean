-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle
-- name    : GoodReductionJacobian.RelativeGroupLaw.forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/775f9507-277a-57a3-a618-90a0c4b970c0
-- title:
--   Unit-preserving morphisms of abelian schemes are homomorphisms
-- statement:
--   Fix a commutative ring $S$ and schemes $A,B$ with structure morphisms $f : A \to \operatorname{Spec} S$ and $g : B \to \operatorname{Spec} S$, together with relative group laws `LA` on $f$ and `LB` on $g$: for each scheme $T$ and each $t : T \to \operatorname{Spec} S$ a group structure (multiplication, unit, inverse, with associativity, two-sided unit law and left inverse law) on the set $\{\,x : T \to A \mid x \circ f = t\,\}$ of $T$-points of $f$ over $t$, the multiplications being natural under precomposition with morphisms $\psi : T' \to T$ over the base. Both laws are assumed commutative, and $f$ and $g$ are assumed to satisfy `AbelianSchemePropertyBundle`, i.e. to be smooth and proper with set-theoretically connected fibres over each point of $\operatorname{Spec} S$ and to admit some relative group law. Let $S'$ be a commutative ring, $s : \operatorname{Spec} S' \to \operatorname{Spec} S$, and let $\varphi : A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to B$ satisfy $\varphi$ followed by $g$ equals the second projection followed by $s$. Then the following are equivalent: (i) for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all $T$-points $P,Q$ of $f$ over $t' \circ s$, the canonical lift of $(\,\mathrm{mul}(P,Q),t'\,)$ to the fibre product, followed by $\varphi$, equals the `LB`-product of the lifts of $P$ and of $Q$ each followed by $\varphi$; (ii) the lift of the unit point $\mathrm{one}(s)$ of $f$ over $s$ together with the identity of $\operatorname{Spec} S'$, followed by $\varphi$, equals the unit point $\mathrm{one}(s)$ of $g$ over $s$.
--
--   This is the standard homomorphism criterion for abelian schemes — a morphism over the base is compatible with the group laws as soon as it carries the unit section to the unit section — in the functor-of-points form needed to exhibit $\mathrm{Hom}(A,B)$ as a subfunctor of the Mor-functor. It is used in the construction of a scheme representing the relevant Hilbert-scheme pieces for such morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle
    (S : Type) [CommRing S] {A B : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of S)) (g : B ⟶ Spec (CommRingCat.of S))
    (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)
    (hAc : LA.IsCommutative) (hBc : LB.IsCommutative)
    (hA : AbelianSchemePropertyBundle S f) (hB : AbelianSchemePropertyBundle S g)
    (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
          (LB.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) ↔
      pullback.lift (LA.one s).1 (𝟙 _) (by rw [Category.id_comp]; exact (LA.one s).2) ≫ φ = (LB.one s).1 := by sorry
