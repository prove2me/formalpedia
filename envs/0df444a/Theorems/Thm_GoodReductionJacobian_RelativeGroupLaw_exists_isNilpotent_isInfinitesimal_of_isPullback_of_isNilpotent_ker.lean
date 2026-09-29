-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/27c72965-9c00-5ece-813d-dc8db4d3678a
-- title:
--   Infinitesimal q-power torsion ascends a nilpotent thickening
-- statement:
--   Fix a natural number $q$ and commutative rings $B$, $B_0$ with $B_0$ a $B$-algebra whose structure map $B \to B_0$ is surjective with nilpotent kernel (the ideal $\ker(B\to B_0)$ satisfies $\mathrm{IsNilpotent}$). Let $f \colon A \to \operatorname{Spec} B$ be a morphism of schemes equipped with a relative group law $L$, that is, a group structure on the sets of sections $\{\varphi \colon T \to A \mid \varphi \cdot f = t\}$ for every $t \colon T \to \operatorname{Spec} B$, natural in $T$; likewise $f_0 \colon A_0 \to \operatorname{Spec} B_0$ with a relative group law $L_0$. Assume given $g \colon A_0 \to A$ making the square with $f_0$, $f$ and $\operatorname{Spec}(B \to B_0)$ cartesian, and such that for every $t \colon T \to \operatorname{Spec} B_0$ and all sections $P, Q$ over $t$ the composite of $L_0.\mathrm{mul}\,t\,P\,Q$ with $g$ is the $L$-product of $P \cdot g$ and $Q \cdot g$ over $t$ followed by $\operatorname{Spec}(B \to B_0)$. Assume further that $q$-power torsion is infinitesimal over $B_0$: for every $B_0$-algebra $C$, every $m$ and every section $P$ of $f_0$ over the structure morphism $\operatorname{Spec} C \to \operatorname{Spec} B_0$ with $q^m$-fold $L_0$-multiple (iterated $L_0.\mathrm{mul}$ starting from the unit section) equal to the unit section, there is an ideal $J \subseteq C$ with $J$ nilpotent such that $P$ pulled back along $\operatorname{Spec}(C \to C/J)$ is the unit section of $L_0$. Then the same conclusion holds over $B$: for every $B$-algebra $C$, every $m$, and every section $P$ of $f$ over $\operatorname{Spec} C \to \operatorname{Spec} B$ whose $q^m$-fold $L$-multiple is the unit section, there is a nilpotent ideal $J \subseteq C$ with $P$ reducing to the unit section of $L$ over $\operatorname{Spec}(C/J)$.
--
--   This is the statement that infinitesimality (connectedness) of the $q$-power torsion is insensitive to nilpotent thickenings of the base, in the pointwise form in which it is consumed by the Serre–Tate style lifting and formal-coordinate results for relative group laws. It is used in the construction of formal coordinates on deformations over Artinian bases and in transporting the quaternionic action to deformations of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker
    (q : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of B)) (L : RelativeGroupLaw B f)
    {A₀ : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)) (L₀ : RelativeGroupLaw B₀ f₀)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (hgmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ g =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hinf₀ : ∀ (C : Type) [CommRing C] [Algebra B₀ C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B₀) C) f₀),
      nsmulPt L₀ (Scheme.specOver (𝒪 := B₀) C) (q ^ m) P = L₀.one (Scheme.specOver (𝒪 := B₀) C) →
        ∃ J : Ideal C, IsNilpotent J ∧ L₀.IsInfinitesimal J P)
    (C : Type) [CommRing C] [Algebra B C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B) C) f)
    (hP : nsmulPt L (Scheme.specOver (𝒪 := B) C) (q ^ m) P = L.one (Scheme.specOver (𝒪 := B) C)) :
    ∃ J : Ideal C, IsNilpotent J ∧ L.IsInfinitesimal J P := by sorry
