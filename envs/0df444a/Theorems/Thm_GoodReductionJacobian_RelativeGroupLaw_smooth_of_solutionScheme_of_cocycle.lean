-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle
-- name    : GoodReductionJacobian.RelativeGroupLaw.smooth_of_solutionScheme_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/514551f3-783f-5599-8e5a-aefc25899dfe
-- title:
--   Smoothness of the solution scheme of a cocycle
-- statement:
--   Let $R$ be a commutative ring, let $g_N : N \to \operatorname{Spec} R$ be a smooth morphism of schemes and let $L$ be a relative group law for $g_N$: a rule assigning to each $t : T \to \operatorname{Spec} R$ a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the set of $\varphi : T \to N$ with $\varphi \circ$ (i.e. $\varphi$ followed by) $g_N$ equal to $t$, compatible with composition $x \mapsto \psi \circ x$ along any $\psi : T' \to T$ over $\operatorname{Spec} R$. Let $R'$ be a nontrivial finite free $R$-algebra, $q : S' := \operatorname{Spec} R' \to \operatorname{Spec} R$ the induced morphism, and let $j : \operatorname{Spec} A_0 \to N$ be an open immersion over $\operatorname{Spec} R$ with $A_0$ an $R$-algebra of finite type. Let $g$ be a section of $g_N$ over $S' \times_R S'$ (with structure morphism the first projection followed by $q$) satisfying the cocycle identity $\mathrm{pr}_{12}^* g \cdot \mathrm{pr}_{23}^* g = \mathrm{pr}_{13}^* g$ on $S' \times_R S' \times_R S'$, the products being formed with $L$. Let $g_P : P \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$ and $u$ a section of $g_N$ over $S' \times_R P$. Call a section $h$ of $g_N$ over $S' \times_R T$ a solution if the image of the underlying map of $h$ lies in the image of $j$, the same holds for the section $\mathrm{pr}_{12}^* g \cdot \mathrm{pr}_{23}^* h$ over $(S' \times_R S') \times_R T$, and $\mathrm{pr}_{13}^* h = \mathrm{pr}_{12}^* g \cdot \mathrm{pr}_{23}^* h$ there. Assume $u$ is a solution, and that $u$ is universal: for every $t : T \to \operatorname{Spec} R$ and every solution $h$ over $S' \times_R T$ there is a unique $x : T \to P$ over $\operatorname{Spec} R$ with $(\mathrm{id}_{S'} \times x)^* u = h$. Then $g_P$ is smooth.
--
--   This is the smoothness half of faithfully flat descent for the twisted form cut out by a Čech $1$-cocycle: the scheme representing solutions of $\mathrm{pr}_1^* h = g \cdot \mathrm{pr}_2^* h$ inside the affine chart $\operatorname{Spec} A_0$ of $N$ is smooth over the base. It is used in the construction of Néron models of Jacobians, in the step producing, over a Henselian local ring, a section trivialising the cocycle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_solutionScheme_of_cocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.smooth_of_solutionScheme_of_cocycle
    {R : Type} [CommRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN) [Smooth gN]
    (R' : Type) [CommRing R'] [Algebra R R'] [Nontrivial R'] [Module.Finite R R'] [Module.Free R R']
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
    Smooth gP := by sorry
