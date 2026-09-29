-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_residueField_point_solutionScheme_of_cocycle
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_residueField_point_solutionScheme_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/ccd77e59-c11f-54a7-b6fe-c60b5cd4f944
-- title:
--   Residue-field point of a representing solution scheme
-- statement:
--   Let $R$ be a local commutative ring whose residue field $\kappa =$ `IsLocalRing.ResidueField R` is algebraically closed, let $gN : N \to \operatorname{Spec} R$ be a scheme over $R$ and let $L$ be a `RelativeGroupLaw` for $gN$, i.e. for every $t : T \to \operatorname{Spec} R$ a group structure (multiplication, unit, inverse, with associativity, both unit laws, left inverse law) on the set of pairs $\langle\varphi : T \to N,\ \varphi \text{ followed by } gN = t\rangle$, compatible with precomposition along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $R'$ be a local $R$-algebra, finite and free as an $R$-module, and $q : \operatorname{Spec} R' \to \operatorname{Spec} R$ the morphism induced by $R \to R'$. Let $A_0$ be an $R$-algebra of finite type together with an open immersion $j : \operatorname{Spec} A_0 \to N$ over $\operatorname{Spec} R$ (a chart). Let $g$ be a morphism $\operatorname{Spec} R' \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to N$ lying over the first projection followed by $q$, and assume the Čech cocycle identity on the triple fibre product: the $L$-product of the pullbacks of $g$ along the two outer projections equals the pullback of $g$ along the morphism to $\operatorname{Spec} R' \times \operatorname{Spec} R'$ given by the first and last coordinates. Assume the unit section $L.\mathrm{one}(\mathrm{id}_{\operatorname{Spec} R})$ has topological image inside the image of $j$. Finally let $gP : P \to \operatorname{Spec} R$ and let $u$ be a morphism $\operatorname{Spec} R' \times_{\operatorname{Spec} R} P \to N$ over the first projection followed by $q$ such that: (i) the image of $u$ lies in the image of $j$, as does the image of the $L$-product of the pullback of $g$ with the pullback of $u$ along the second projection; and the two pullbacks of $u$ to $(\operatorname{Spec} R' \times \operatorname{Spec} R') \times_{\operatorname{Spec} R} P$ are related by $\mathrm{pr}_1^* u = g \cdot \mathrm{pr}_2^* u$; and (ii) $(P, gP, u)$ represents the corresponding functor: for every $t : T \to \operatorname{Spec} R$ and every $h : \operatorname{Spec} R' \times_{\operatorname{Spec} R} T \to N$ over the first projection followed by $q$ satisfying the same three conditions, there is a unique morphism $x : T \to P$ over $\operatorname{Spec} R$ whose base change $\mathrm{id} \times x$ composed with $u$ equals $h$. Then there exists $x_0 : \operatorname{Spec} \kappa \to P$ with $x_0$ followed by $gP$ equal to $\operatorname{Spec}$ of the structure map $R \to \kappa$, i.e. a $\kappa$-point of $P$ over $\operatorname{Spec} R$.
--
--   This is the existence of a point in the closed fibre of the scheme representing the descent (solution) functor attached to a Čech $1$-cocycle for a finite free local cover $\operatorname{Spec} R' \to \operatorname{Spec} R$, with values in a relative group law. It is the geometric input for splitting such a cocycle as a coboundary, used in the descent step for Néron models of Jacobians via `exists_eq_mul_inv_of_cocycle_of_isLocalRing_of_smooth_of_henselianLocalRing`; it cites the structure of finite flat local extensions over a ring with algebraically closed residue field and the vanishing of the cocycle on the diagonal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_residueField_point_solutionScheme_of_cocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_residueField_point_solutionScheme_of_cocycle
    {R : Type} [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
    (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalRing R'] [Module.Finite R R'] [Module.Free R R']
    (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (A₀ : Type) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
    (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j] (hj : j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
    (hg : L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
        (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
          (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
                Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
          (by
            simp only [Category.assoc]
            rw [← pullback.condition (f := q) (g := q),
              ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
              ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
              ← pullback.condition (f := q) (g := q)]))
        (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g)
    (hunit : Set.range (L.one (𝟙 (Spec (CommRingCat.of R)))).1.base ⊆ Set.range j.base)
    (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN)
    (hsol : (Set.range u.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.fst q q) (𝟙 P) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) u) = (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u))))
    (huniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst q t ≫ q) gN),
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
              (by rw [pullback.lift_fst_assoc, Category.comp_id]) u) = h) :
    ∃ x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ P,
      x₀ ≫ gP = Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) := by sorry
