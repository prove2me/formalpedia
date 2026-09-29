-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_forall_comp_act_eq_of_separabilityElement_of_ker_mul_ker_eq_bot_of_isAlgClosed
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isPullback_forall_comp_act_eq_of_separabilityElement_of_ker_mul_ker_eq_bot_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/b866fbdf-2da0-5e04-abe4-e6a45966c599
-- title:
--   Λ-equivariant lifting of abelian schemes along square-zero surjections
-- statement:
--   Let $S$ be an Artinian local ring whose residue field is algebraically closed of characteristic $\ell$ for a prime $\ell$, let $p : S \to S_0$ be a surjective ring homomorphism with $(\ker p)^2 = \bot$, and let $\Lambda$ be an associative unital ring admitting a separability element, namely an $e \in (S \otimes_{\mathbb Z} \Lambda) \otimes_S (S \otimes_{\mathbb Z} \Lambda)$ with multiplication map value $1$ and $(x \otimes 1)e = e(1 \otimes x)$ for all $x \in S \otimes_{\mathbb Z} \Lambda$ (in the form: $e$ is invariant under left multiplication by $x$ in the first factor versus right multiplication by $x$ in the second). Let $f_0 : A_0 \to \operatorname{Spec} S_0$ carry a relative group law $L_0$ (a functorial group structure on the sets $\{\varphi : T \to A_0 \mid \varphi \circ f_0 = t\}$, natural in $t$) which is commutative, satisfy the bundle of properties "smooth, proper, all fibres connected, and a relative group law exists", and have all fibres $f_0^{-1}(s)$ of topological Krull dimension $d$; and let $\mathrm{act}_0 : \Lambda \to \operatorname{End}(A_0)$ consist of endomorphisms over $\operatorname{Spec} S_0$ which are homomorphisms for $L_0$ on points, with $\mathrm{act}_0(1) = \mathrm{id}$, $\mathrm{act}_0(xy) = \mathrm{act}_0(x) \circ \mathrm{act}_0(y)$ (composition in diagrammatic order: $\mathrm{act}_0 y$ followed by $\mathrm{act}_0 x$ reversed, i.e. $\mathrm{act}_0(xy) = \mathrm{act}_0(y) \!\!\gg\!\! \mathrm{act}_0(x)$), and $\mathrm{act}_0(x+y)$ equal on points to the $L_0$-product of $\mathrm{act}_0(x)$ and $\mathrm{act}_0(y)$. Then there are a scheme $A$, a morphism $f : A \to \operatorname{Spec} S$, a relative group law $L$ for $f$, a morphism $g : A_0 \to A$ making the square with $f_0$, $f$ and $\operatorname{Spec}(p)$ cartesian, and $\mathrm{act} : \Lambda \to \operatorname{End}(A)$ over $\operatorname{Spec} S$, such that $L$ is commutative, $f$ satisfies the same bundle of properties, every fibre of $f$ has topological Krull dimension $d$, $g$ is a homomorphism on points from $L_0$ to the base change of $L$ along $\operatorname{Spec}(p)$, each $\mathrm{act}(x)$ is a homomorphism for $L$ on points, $\mathrm{act}(1) = \mathrm{id}$, $\mathrm{act}(xy) = \mathrm{act}(y)$ followed by $\mathrm{act}(x)$, $\mathrm{act}(x+y)$ is on points the $L$-product of $\mathrm{act}(x)$ and $\mathrm{act}(y)$, and $\mathrm{act}_0(x)$ followed by $g$ equals $g$ followed by $\mathrm{act}(x)$ for every $x \in \Lambda$.
--
--   This is the equivariant infinitesimal lifting theorem for abelian schemes with an action of a ring $\Lambda$ which is separable after base change to $S$: any such abelian scheme over $S_0$ lifts, together with its $\Lambda$-action and its relative dimension, across a surjection with square-zero kernel. It strengthens the companion statement in which the kernel is additionally required to annihilate the maximal ideal of $S$, which it cites, and is used in the construction of bare deformations of fake elliptic curves with an action of a maximal order in a quaternion algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_forall_comp_act_eq_of_separabilityElement_of_ker_mul_ker_eq_bot_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isPullback_forall_comp_act_eq_of_separabilityElement_of_ker_mul_ker_eq_bot_of_isAlgClosed
    {S S₀ : Type} [CommRing S] [CommRing S₀]

    [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)] (ℓ : ℕ) [Fact ℓ.Prime] [CharP (IsLocalRing.ResidueField S) ℓ]
    (p : S →+* S₀) (hp : Function.Surjective p)
    (hI : RingHom.ker p * RingHom.ker p = ⊥)
    {Λ : Type} [Ring Λ]
    (e : (S ⊗[ℤ] Λ) ⊗[S] (S ⊗[ℤ] Λ)) (he₁ : LinearMap.mul' S (S ⊗[ℤ] Λ) e = 1)
    (he₂ : ∀ x : S ⊗[ℤ] Λ, TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
      TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e)
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)} (L₀ : RelativeGroupLaw S₀ f₀)
    (hL₀ : L₀.IsCommutative) (h₀ : AbelianSchemePropertyBundle S₀ f₀) (d : ℕ)
    (hd : ∀ s : ↥(Spec (CommRingCat.of S₀)), topologicalKrullDim ↥(f₀.base ⁻¹' {s}) = d)
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
          ⟨P.1 ≫ act₀ y, by rw [Category.assoc, act₀_over, P.2]⟩).1) :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
      (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom p)))
      (act : Λ → (A ⟶ A)) (act_over : ∀ x : Λ, act x ≫ f = f),
      L.IsCommutative ∧ AbelianSchemePropertyBundle S f ∧
      (∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = d) ∧
      (∀ {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t₀ f₀),
        (L₀.mul t₀ P Q).1 ≫ g =
          (L.mul (t₀ ≫ Spec.map (CommRingCat.ofHom p))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        (L.mul t P Q).1 ≫ act x =
          (L.mul t ⟨P.1 ≫ act x, by rw [Category.assoc, act_over, P.2]⟩
            ⟨Q.1 ≫ act x, by rw [Category.assoc, act_over, Q.2]⟩).1) ∧
      act 1 = 𝟙 A ∧
      (∀ x y : Λ, act (x * y) = act y ≫ act x) ∧
      (∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
        P.1 ≫ act (x + y) =
          (L.mul t ⟨P.1 ≫ act x, by rw [Category.assoc, act_over, P.2]⟩
            ⟨P.1 ≫ act y, by rw [Category.assoc, act_over, P.2]⟩).1) ∧
      ∀ x : Λ, act₀ x ≫ g = g ≫ act x := by sorry
