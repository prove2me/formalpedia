-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_forall_comp_act_eq_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot_of_isAlgClosed
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isPullback_forall_comp_act_eq_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/624f9c77-59df-5b18-b536-4e99d8e099ac
-- title:
--   Equivariant lifting of abelian schemes along a small surjection
-- statement:
--   Let $S$ be an Artinian local ring whose residue field is algebraically closed of characteristic a prime $\ell$, let $S_0$ be a commutative ring and let $p : S \to S_0$ be a surjective ring homomorphism whose kernel $I = \ker p$ satisfies $I \cdot I = 0$ and $I \cdot \mathfrak m_S = 0$. Let $\Lambda$ be a ring and let $e \in (S \otimes_{\mathbb Z} \Lambda) \otimes_S (S \otimes_{\mathbb Z} \Lambda)$ be an element with $\mathrm{mul}'(e) = 1$ and $(x \otimes 1)\,e = e\,(1 \otimes x)$ for every $x \in S \otimes_{\mathbb Z} \Lambda$, i.e. a separability element. Let $f_0 : A_0 \to \operatorname{Spec} S_0$ be a morphism of schemes carrying a relative group law $L_0$ (a group structure on $T$-points $\mathrm{SchemeHomOver}\,t\,f_0$, natural in $T \to \operatorname{Spec} S_0$) which is commutative, satisfying the bundle of properties `AbelianSchemePropertyBundle`: $f_0$ smooth, proper, with connected fibres and admitting a relative group law; assume each fibre of $f_0$ has topological Krull dimension $d$. Let $\mathrm{act}_0 : \Lambda \to \mathrm{End}(A_0)$ consist of morphisms over $\operatorname{Spec} S_0$ that are additive on points for $L_0$, send $1$ to $\mathrm{id}$, satisfy $\mathrm{act}_0(xy) = \mathrm{act}_0(y) \circ \mathrm{act}_0(x)$ in diagrammatic order, and with $P \cdot \mathrm{act}_0(x+y)$ the $L_0$-product of $P \cdot \mathrm{act}_0(x)$ and $P \cdot \mathrm{act}_0(y)$ on points. Then there exist a scheme $A$, a morphism $f : A \to \operatorname{Spec} S$, a relative group law $L$ on $f$, a morphism $g : A_0 \to A$ making the square with $f_0$, $f$ and $\operatorname{Spec}(p)$ a pullback, and maps $\mathrm{act} : \Lambda \to \mathrm{End}(A)$ over $f$, such that $L$ is commutative, $f$ satisfies `AbelianSchemePropertyBundle`, every fibre of $f$ has topological Krull dimension $d$, $g$ is a homomorphism on points from $L_0$ to $L$, $\mathrm{act}$ satisfies the same point-wise additivity, unit, anti-multiplicativity and $x+y$ identities as $\mathrm{act}_0$, and $\mathrm{act}_0(x)$ followed by $g$ equals $g$ followed by $\mathrm{act}(x)$ for all $x \in \Lambda$.
--
--   This is the infinitesimal lifting step for abelian schemes with multiplication by a separable coefficient ring: along a small surjection of Artinian local rings the abelian scheme, its commutative group law, its relative dimension and its $\Lambda$-action all lift, compatibly with the base change. It feeds the lifting of abelian schemes with quaternionic multiplication along a general square-zero surjection, obtained by iterating this small case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_forall_comp_act_eq_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isPullback_forall_comp_act_eq_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot_of_isAlgClosed
    {S S₀ : Type} [CommRing S] [CommRing S₀]

    [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)] (ℓ : ℕ) [Fact ℓ.Prime] [CharP (IsLocalRing.ResidueField S) ℓ]
    (p : S →+* S₀) (hp : Function.Surjective p)
    (hI : RingHom.ker p * RingHom.ker p = ⊥)

    (hsmall : RingHom.ker p * IsLocalRing.maximalIdeal S = ⊥)
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
