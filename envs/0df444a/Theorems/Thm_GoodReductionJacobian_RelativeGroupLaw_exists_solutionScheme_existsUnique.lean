-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_solutionScheme_existsUnique
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_solutionScheme_existsUnique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/4009e390-d959-54be-a9bf-c28b48cdc8ed
-- title:
--   Representability of the coboundary-solution functor inside an affine chart
-- statement:
--   Let $R$ be a commutative ring, let $gN : N \to \operatorname{Spec} R$ be a scheme over $R$ and let $L$ be a relative group law on $gN$: a group structure on each set $\{\varphi : T \to N \mid \varphi \circ \!\!\text{(as } \varphi \gg gN) = t\}$ of $T$-points of $N$ over a given $t : T \to \operatorname{Spec} R$, with multiplication, unit and inverse satisfying associativity, unit and inverse laws and compatible with composition $x \mapsto \psi \gg x$ along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $R'$ be a finite free $R$-algebra, $q : \operatorname{Spec} R' \to \operatorname{Spec} R$ the morphism induced by the structure map, let $A_0$ be an $R$-algebra of finite type and $j : \operatorname{Spec} A_0 \to N$ an open immersion over $\operatorname{Spec} R$, and let $g$ be a point of $N$ over $S'' := \operatorname{Spec} R' \times_{\operatorname{Spec} R} \operatorname{Spec} R'$, taken with structure morphism the first projection followed by $q$. Call a point $h$ of $N$ over $S' \times_R T$ (with $S' := \operatorname{Spec} R'$, structure morphism the first projection followed by $q$) a solution over $t : T \to \operatorname{Spec} R$ when the set-theoretic image of $h$ lies in the image of $j$, the image of $L$-product of the pullback of $g$ along the projection $S'' \times_R T \to S''$ with the pullback of $h$ along the map $S'' \times_R T \to S' \times_R T$ induced by $\mathrm{pr}_2 : S'' \to S'$ lies in the image of $j$, and the pullback of $h$ along the map induced by $\mathrm{pr}_1 : S'' \to S'$ equals that product. The assertion is that there exist a scheme $P$, a morphism $gP : P \to \operatorname{Spec} R$ and a solution $u$ over $gP$ such that for every scheme $T$, every $t : T \to \operatorname{Spec} R$ and every solution $h$ over $t$ there is a unique $T$-point $x : T \to P$ over $\operatorname{Spec} R$ whose pullback of $u$ along $\mathrm{id}_{S'} \times x$ equals $h$.
--
--   This is the representability of the functor of solutions of the coboundary equation $\mathrm{pr}_1^* h = g \cdot \mathrm{pr}_2^* h$ constrained to lie in a fixed affine chart of $N$, the universal object $P$ being carved out of an affine Weil restriction of $\operatorname{Spec} A_0 \times_R S'$ over $R' / R$. It is used in the descent step [`GoodReductionJacobian.RelativeGroupLaw.exists_eq_mul_inv_of_cocycle_of_isLocalRing_of_smooth_of_henselianLocalRing`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_eq_mul_inv_of_cocycle_of_isLocalRing_of_smooth_of_henselianLocalRing), where a cocycle over a finite free extension is trivialised after passing to a henselian local base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_solutionScheme_existsUnique.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_solutionScheme_existsUnique
    {R : Type} [CommRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
    (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R']
    (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (A₀ : Type) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
    (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j] (hj : j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (g : SchemeHomOver (pullback.fst q q ≫ q) gN) :
    ∃ (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN),
      (Set.range u.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.fst q q) (𝟙 P) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) u) = (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u))) ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst q t ≫ q) gN),
        (Set.range h.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) h) = (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h))) →
        ∃! x : SchemeHomOver t gP, (GoodReductionJacobian.schemeHomOverComp
              (pullback.map q t q gP (𝟙 _) x.1 (𝟙 _) (by simp) (by simpa using x.2.symm))
              (by rw [pullback.lift_fst_assoc, Category.comp_id]) u) = h := by sorry
