-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_act_of_forall_exists_comp_eq_comp_of_isArtinianRing
-- name    : GoodReductionJacobian.BareDeformation.exists_act_of_forall_exists_comp_eq_comp_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/e30fa26d-bcc1-5c8c-9579-49770c5e6c34
-- title:
--   Lifting a ring action to a bare deformation
-- statement:
--   Let $S$ be an Artinian local commutative ring, $S_0$ a commutative $S$-algebra whose structure map $S \to S_0$ is surjective with nilpotent kernel ideal. Let $f_0 : A_0 \to \operatorname{Spec} S_0$ be a morphism of schemes carrying a relative group law $L_0$ (a functorial group structure on the sets $\{\varphi : T \to A_0 \mid \varphi \circ f_0 = t\}$ of points over arbitrary bases $t : T \to \operatorname{Spec} S_0$, natural in $T$), assumed commutative, and satisfying `AbelianSchemePropertyBundle`: $f_0$ is smooth and proper, each fibre of the underlying map is connected, and a relative group law exists. Let $\Lambda$ be a ring and $\mathrm{act}_0 : \Lambda \to \operatorname{End}(A_0)$ satisfy: each $\mathrm{act}_0(x)$ is over $f_0$; each is a homomorphism for $L_0$ on points; $\mathrm{act}_0(1) = \mathrm{id}$; $\mathrm{act}_0(xy) = \mathrm{act}_0(x) \circ \mathrm{act}_0(y)$; and $P \circ \mathrm{act}_0(x+y) = L_0$-product of $P \circ \mathrm{act}_0(x)$ and $P \circ \mathrm{act}_0(y)$ on points. Let $D$ be a bare deformation of $(f_0, L_0)$ over $S$: a scheme $A$ over $\operatorname{Spec} S$ with commutative relative group law $L$, the same property bundle, and $g : A_0 \to A$ making $A_0$ the pullback along $\operatorname{Spec}(S \to S_0)$ and a homomorphism on points. If for each $x \in \Lambda$ some $\varphi : A \to A$ over $\operatorname{Spec} S$ satisfies $\mathrm{act}_0(x)$ followed by $g$ equals $g$ followed by $\varphi$, then there is a map $\mathrm{act} : \Lambda \to \operatorname{End}(A)$ with all morphisms over $\operatorname{Spec} S$, satisfying the same four laws for $L$, and with $\mathrm{act}_0(x)$ followed by $g$ equal to $g$ followed by $\mathrm{act}(x)$ for all $x$.
--
--   This is the rigidity-based statement that individually chosen lifts of the endomorphisms of a $\Lambda$-action on the special fibre can be normalised and assembled into a genuine $\Lambda$-action by group-law homomorphisms on a bare deformation over an Artinian local base. It is used in the construction of deformations of Jacobians equipped with an action, where the lifted action is produced together with the pullback square over an algebraically closed residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_act_of_forall_exists_comp_eq_comp_of_isArtinianRing.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe v

theorem GoodReductionJacobian.BareDeformation.exists_act_of_forall_exists_comp_eq_comp_of_isArtinianRing
    (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)} (L₀ : RelativeGroupLaw S₀ f₀)
    (hL₀ : L₀.IsCommutative) (h₀ : AbelianSchemePropertyBundle S₀ f₀)
    {Λ : Type v} [Ring Λ]
    (act₀ : Λ → (A₀ ⟶ A₀)) (act₀_over : ∀ x : Λ, act₀ x ≫ f₀ = f₀)
    (act₀_hom : ∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ act₀ x =
        (L₀.mul t ⟨P.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, P.2]⟩
          ⟨Q.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, Q.2]⟩).1)
    (act₀_one : act₀ 1 = 𝟙 A₀)
    (act₀_mul : ∀ x y : Λ, act₀ (x * y) = act₀ y ≫ act₀ x)
    (act₀_add : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t f₀),
      P.1 ≫ act₀ (x + y) =
        (L₀.mul t ⟨P.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, P.2]⟩
          ⟨P.1 ≫ act₀ y, by rw [Category.assoc, act₀_over, P.2]⟩).1)
    (D : BareDeformation f₀ L₀ S)
    (hlift : ∀ x : Λ, ∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ act₀ x ≫ D.g = D.g ≫ φ) :
    ∃ (act : Λ → (D.A ⟶ D.A)) (act_over : ∀ x : Λ, act x ≫ D.f = D.f),
      (∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t D.f),
        (D.L.mul t P Q).1 ≫ act x =
          (D.L.mul t ⟨P.1 ≫ act x, by rw [Category.assoc, act_over, P.2]⟩
            ⟨Q.1 ≫ act x, by rw [Category.assoc, act_over, Q.2]⟩).1) ∧
      act 1 = 𝟙 D.A ∧
      (∀ x y : Λ, act (x * y) = act y ≫ act x) ∧
      (∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t D.f),
        P.1 ≫ act (x + y) =
          (D.L.mul t ⟨P.1 ≫ act x, by rw [Category.assoc, act_over, P.2]⟩
            ⟨P.1 ≫ act y, by rw [Category.assoc, act_over, P.2]⟩).1) ∧
      ∀ x : Λ, act₀ x ≫ D.g = D.g ≫ act x := by sorry
