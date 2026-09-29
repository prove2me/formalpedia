-- Prove2me | Theorems.Thm_GoodReductionJacobian_lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
-- name    : GoodReductionJacobian.lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/0fac3640-4014-5a40-9138-0aa73bc0e393
-- title:
--   Group axioms over a complete base from levelwise laws
-- statement:
--   Let $R$ be a noetherian commutative ring and $I \subseteq R$ an ideal such that $R$ is $I$-adically complete. Let $f : A \to \operatorname{Spec} R$ be a scheme over $R$ admitting a closed immersion $\iota : A \to \mathbb{P}^N_R$ (into the $\operatorname{Proj}$ of the homogeneous submodule construction on $N+1$ variables) with $\iota$ followed by the structure map of $\mathbb{P}^N_R$ equal to $f$, and let $e$ be a section of $f$, i.e. a morphism $\operatorname{Spec} R \to A$ whose composite with $f$ is the identity. For each $n$ write $A_n = A \times_{\operatorname{Spec} R} \operatorname{Spec}(R/I^{n+1})$ with structure morphism `adicThickeningToBase f I n` to $\operatorname{Spec}(R/I^{n+1})$ and canonical morphism `adicThickeningι f I n` : $A_n \to A$. Assume given, for every $n$, a `RelativeGroupLaw` $L_n$ on $A_n$ over $R/I^{n+1}$, that is, operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on $T$-points of $A_n$ over each $t : T \to \operatorname{Spec}(R/I^{n+1})$ satisfying associativity, both unit laws, left inverse and naturality of multiplication in $T$. Assume further: the unit point of $L_n$ at the identity of $\operatorname{Spec}(R/I^{n+1})$, pushed into $A$, is the base change of $e$ along $R \to R/I^{n+1}$; a morphism $m : A \times_{\operatorname{Spec} R} A \to A$ over $R$ (its composite with $f$ being the first projection followed by $f$) which, for every $n$, every $t : T \to \operatorname{Spec}(R/I^{n+1})$ and all points $x, y$ of $A_n$ over $t$, sends the pair $(x,y)$ (mapped into $A$) to $L_n$'s product $\mathrm{mul}\,t\,x\,y$; and a morphism $i : A \to A$ over $R$ which likewise computes $L_n$'s inversion on all such points. Then the four group identities hold on the nose: $(e \circ f, \mathrm{id}_A)$ followed by $m$ is $\mathrm{id}_A$; $(\mathrm{id}_A, e \circ f)$ followed by $m$ is $\mathrm{id}_A$; the two bracketings of $m$ on $(A \times_{\operatorname{Spec} R} A) \times_{\operatorname{Spec} R} A$ agree; and $(i, \mathrm{id}_A)$ followed by $m$ equals $e \circ f$.
--
--   This is the formal-completion step in the construction of a group law on a scheme over a complete base: identities between morphisms into a projective $R$-scheme may be checked on the tower of $I$-adic thickenings, where they follow from the axioms of the levelwise relative group laws. It is used to produce a `RelativeGroupLaw` on $A$ itself whose unit is the given section $e$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.lean

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

theorem GoodReductionJacobian.lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))
    (hone : ∀ n : ℕ, ((L n).one (𝟙 _)).1 ≫ adicThickeningι f I n = adicThickeningBase I n ≫ e.1)
    (m : pullback f f ⟶ A) (hm : m ≫ f = pullback.fst f f ≫ f)
    (hmul : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x y : SchemeHomOver t (adicThickeningToBase f I n)),
        pullback.lift (x.1 ≫ adicThickeningι f I n) (y.1 ≫ adicThickeningι f I n)
            (by rw [Category.assoc, Category.assoc, adicThickeningι_comp, ← Category.assoc, ← Category.assoc, x.2, y.2]) ≫ m =
          ((L n).mul t x y).1 ≫ adicThickeningι f I n)
    (i : A ⟶ A) (hi : i ≫ f = f)
    (hinv : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x : SchemeHomOver t (adicThickeningToBase f I n)),
        x.1 ≫ adicThickeningι f I n ≫ i = ((L n).inv t x).1 ≫ adicThickeningι f I n) :
    pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A ∧
    pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A ∧
    pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ m) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, hm]; exact pullback.condition) ≫ m =
        pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f)
          (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
              (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m)
          (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc,
                ← pullback.condition (f := f) (g := f)]) ≫ m ∧
    pullback.lift i (𝟙 A) (by rw [hi, Category.id_comp]) ≫ m = f ≫ e.1 := by sorry
