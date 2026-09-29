-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_mul_eq_inv_eq_of_comp_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_mul_eq_inv_eq_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/28f97343-310d-5c40-9bf9-bbaf10465e4c
-- title:
--   Relative group law from unital associative multiplication morphisms
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism. Let $e$ be a section of $f$, i.e. a morphism $e_1 : \operatorname{Spec} R \to A$ together with $e_1 \circ$ (followed by) $f$ equal to the identity, and let $m : A \times_f A \to A$ be a morphism from the fibre product of $f$ with itself satisfying $m$ followed by $f$ equals the first projection followed by $f$. Assume: the lift of $(f \text{ followed by } e_1, \mathrm{id}_A)$ followed by $m$ is $\mathrm{id}_A$, and likewise for $(\mathrm{id}_A, f \text{ followed by } e_1)$; the usual associativity identity for $m$ on the triple fibre product, formulated via the pullback of $\mathrm{pr}_1 \circ f$ along $f$; and there is $i : A \to A$ with $i$ followed by $f$ equal to $f$ such that the lift of $(i, \mathrm{id}_A)$ followed by $m$ equals $f$ followed by $e_1$. The conclusion asserts the existence of a term $L$ of type `RelativeGroupLaw R f` — that is, for every scheme $T$ and every $t : T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set of $\phi : T \to A$ with $\phi$ followed by $f$ equal to $t$, satisfying associativity, both unit laws, left inverses, and compatibility of multiplication with precomposition by morphisms $\psi$ over $\operatorname{Spec} R$ — such that the unit at $t = \mathrm{id}$ is $e$, the multiplication of $x,y$ at any $t$ is the pullback lift of $x, y$ followed by $m$, the inverse of $x$ is $x$ followed by $i$, and moreover any `RelativeGroupLaw R f` whose unit at $\mathrm{id}$ is $e$ and whose multiplication is given by the same formula has, at every $T$, $t$ and $x$, the same unit, the same inverse of $x$, and the same product of $x$ with every $y$.
--
--   This is the functor-of-points translation of the classical fact that a scheme over a base equipped with a multiplication morphism, a unit section and an inverse morphism satisfying the group axioms as identities of morphisms carries a group structure on its $T$-points, natural in $T$, and that this structure is determined by the unit and multiplication. It is used in the construction of relative group laws on schemes of good reduction, where a group law is produced from morphisms obtained by approximation over adic thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_mul_eq_inv_eq_of_comp_eq.lean

import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_mul_eq_inv_eq_of_comp_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (m : pullback f f ⟶ A) (hm : m ≫ f = pullback.fst f f ≫ f)
    (h_one_mul : pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A)
    (h_mul_one : pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A)
    (h_assoc : pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ m) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, hm]; exact pullback.condition) ≫ m =
        pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f)
          (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
              (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m)
          (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc,
                ← pullback.condition (f := f) (g := f)]) ≫ m)
    (i : A ⟶ A) (hi : i ≫ f = f)
    (h_inv_mul : pullback.lift i (𝟙 A) (by rw [hi, Category.id_comp]) ≫ m = f ≫ e.1) :
    ∃ L : RelativeGroupLaw R f, L.one (𝟙 _) = e ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (L.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), (L.inv t x).1 = x.1 ≫ i) ∧
      (∀ L' : RelativeGroupLaw R f, L'.one (𝟙 _) = e →
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
          (L'.mul t x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ m) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
          L'.one t = L.one t ∧ L'.inv t x = L.inv t x ∧ ∀ y, L'.mul t x y = L.mul t x y) := by sorry
