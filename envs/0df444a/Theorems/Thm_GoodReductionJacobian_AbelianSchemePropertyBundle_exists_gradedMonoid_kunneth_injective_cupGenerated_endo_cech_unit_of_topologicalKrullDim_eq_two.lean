-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_gradedMonoid_kunneth_injective_cupGenerated_endo_cech_unit_of_topologicalKrullDim_eq_two
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_gradedMonoid_kunneth_injective_cupGenerated_endo_cech_unit_of_topologicalKrullDim_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/e14dcb56-2bdc-5ded-8e27-1fa7db5a78dd
-- title:
--   Čech–Hopf package with endomorphisms for abelian surfaces
-- statement:
--   Let $k$ be an algebraically closed field, $f \colon A \to \operatorname{Spec} k$ a morphism of schemes, $L$ a relative group law on $f$ (a functorial group structure on the sets $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, natural in $T$), and $hA$ the bundle of properties asserting that $f$ is smooth and proper, has connected fibres, and admits a relative group law. Assume every fibre of $f$ has topological Krull dimension $2$. Let $\mathcal K$ be an ordered affine cover of $A$ (a finite linearly ordered family of affine opens with supremum $\top$) and $\mathcal W$ one of $A \times_k A$, together with index maps $\lambda_1, \lambda_2, \lambda_3$ refining $\mathcal W$ into $\mathcal K$ along the two projections and along the multiplication $m = L.\mathrm{mul}$ of the two projections, in the sense that each $\mathcal W_w$ lies in the corresponding preimage of $\mathcal K_{\lambda_i(w)}$. The conclusion asserts the existence of $k$-algebras $H$, $H'$, a family of $k$-submodules $\mathcal A_n \subseteq H$ forming a graded monoid ($1 \in \mathcal A_0$, $\mathcal A_a \mathcal A_b \subseteq \mathcal A_{a+b}$), $k$-algebra maps $p_1, p_2, m \colon H \to H'$, $k$-linear class maps $\mathrm{cls}_n$ from the $n$-cocycles of the ordered Čech complex of the presheaf `OModulePresheaf.unit f` (the structure sheaf $U \mapsto \Gamma(A,U)$ with its $k$-algebra structure coming from $f$) with respect to $\mathcal K$ to $H$, and $\mathrm{cls}'_n$ likewise for $\mathcal W$ and `OModulePresheaf.unit (pullback.fst f f ≫ f)`, and, for every endomorphism $\varphi$ of $A$ over $\operatorname{Spec} k$, $k$-algebra endomorphisms $\rho(\varphi)$ of $H$ and $\rho_1(\varphi), \rho_2(\varphi)$ of $H'$, subject to the following. The range of $\mathrm{cls}_n$ is $\mathcal A_n$; $\mathrm{cls}_0$ is injective and $\mathrm{cls}_{n+1}$ kills exactly the coboundaries, and the same two properties hold for $\mathrm{cls}'$. The map $\bigoplus_{(a,b) \in \mathbb N \times \mathbb N} \mathcal A_a \otimes_k \mathcal A_b \to H'$, $x \otimes y \mapsto p_1(x)\,p_2(y)$, is injective (Künneth injectivity). One has $p_2(x)p_1(y) = (-1)^{ab} p_1(y)p_2(x)$ for $x \in \mathcal A_a$, $y \in \mathcal A_b$, and $m(x) = p_1(x) + p_2(x)$ for $x \in \mathcal A_1$ (primitivity in degree one). For every cocycle $z$ on $\mathcal K$, the three signed refinement pull-backs `OModulePresheaf.unitPullback` of $z$ to $\mathcal W$ along the two projections and along $m$ are again cocycles, and $p_1(\mathrm{cls}_n z)$, $p_2(\mathrm{cls}_n z)$, $m(\mathrm{cls}_n z)$ are the $\mathrm{cls}'_n$-classes of these three pull-backs. Moreover $\mathcal A_2 \subseteq \mathcal A_1 \cdot \mathcal A_1$. Finally, $\rho(\varphi)$ preserves each $\mathcal A_n$, $\rho(\mathrm{id}_A) = \mathrm{id}_H$, $\rho$ is contravariantly multiplicative, $\rho(\chi) = \rho(\varphi) + \rho(\psi)$ on $\mathcal A_1$ whenever $\chi$ is the $L$-sum of $\varphi$ and $\psi$ on all test points; $\rho(\varphi)$ is pinned to pull-back along $\varphi$, in the sense that $\rho(\varphi)(\mathrm{cls}_{n+1} z) = \mathrm{cls}_{n+1} z'$ whenever, for some ordered affine cover $\mathcal V$ of $A$ with refinement data for $\varphi$ and for $\mathrm{id}_A$, the difference of the two refined pull-backs of $z$ and $z'$ is a coboundary on $\mathcal V$; $\rho_1(\varphi)$ and $\rho_2(\varphi)$ satisfy $\rho_1(\varphi)(p_1 x) = p_1(\rho(\varphi)x)$, $\rho_1(\varphi)(p_2 x) = p_2 x$, $\rho_2(\varphi)(p_1 x) = p_1 x$, $\rho_2(\varphi)(p_2 x) = p_2(\rho(\varphi)x)$, and each is pinned in the same cochain-level sense to pull-back along $\varphi \times \mathrm{id}$, respectively $\mathrm{id} \times \varphi$, on $A \times_k A$.
--
--   This packages the cohomology of the structure sheaf of an abelian surface over an algebraically closed field, computed by ordered Čech cochains, as a graded $k$-algebra generated in degree one, with Künneth injectivity, primitivity of degree-one classes under the group law, and a contravariant, degree-preserving and degree-one-additive action of the endomorphisms of $A$, together with the compatible actions of $\varphi \times \mathrm{id}$ and $\mathrm{id} \times \varphi$ on the square. It is the cohomological input used in the treatment of fake elliptic curves in the Čerednik–Drinfeld setting, where it is cited by the statements on invertibility of pull-back isomorphisms compatible with the Rosati involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_gradedMonoid_kunneth_injective_cupGenerated_endo_cech_unit_of_topologicalKrullDim_eq_two.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_gradedMonoid_kunneth_injective_cupGenerated_endo_cech_unit_of_topologicalKrullDim_eq_two
    (k : Type u) [Field k] [IsAlgClosed k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2)
    (𝒦 : A.OrderedAffineCover)

    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤
      (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ
        𝒦.U (lam₃ w)) :
    ∃ (H : Type u) (_ : Ring H) (_ : Algebra k H) (H' : Type u) (_ : Ring H') (_ : Algebra k H')
      (𝒜 : ℕ → Submodule k H) (_ : SetLike.GradedMonoid 𝒜) (p₁ p₂ m : H →ₐ[k] H')
      (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n)) →ₗ[k] H)
      (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)) →ₗ[k] H')

      (ρ : ∀ φ : A ⟶ A, φ ≫ f = f → (H →ₐ[k] H))
      (ρ₁ ρ₂ : ∀ φ : A ⟶ A, φ ≫ f = f → (H' →ₐ[k] H')),

      (∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n) ∧

      (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 0)), cls 0 z = 0 ↔ z = 0) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 (n + 1)))),
        cls (n + 1) z = 0 ↔
          (z : (OModulePresheaf.unit f).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒦 n)) ∧
      (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0)), cls' 0 z = 0 ↔ z = 0) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (n + 1)))),
        cls' (n + 1) z = 0 ↔
          (z : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 (n + 1)) ∈
            LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)) ∧

      Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
        LinearMap.mul' k H' ∘ₗ
          TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)) ∧

      (∀ (a b : ℕ), ∀ x ∈ 𝒜 a, ∀ y ∈ 𝒜 b, p₂ x * p₁ y = ((-1 : ℤ) ^ (a * b)) • (p₁ y * p₂ x)) ∧

      (∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x) ∧

      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n))),
        ∃ (hz₁ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ n z.1 ∈
              LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
          (hz₂ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ n z.1 ∈
              LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
          (hz₃ : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f)
              (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1
              𝒲 𝒦 lam₃ h₃ n z.1 ∈
              LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)),
          p₁ (cls n z) = cls' n ⟨_, hz₁⟩ ∧ p₂ (cls n z) = cls' n ⟨_, hz₂⟩ ∧ m (cls n z) = cls' n ⟨_, hz₃⟩) ∧

      𝒜 2 ≤ 𝒜 1 * 𝒜 1 ∧

      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f) (n : ℕ), ∀ x ∈ 𝒜 n, ρ φ hφ x ∈ 𝒜 n) ∧
      (ρ (𝟙 A) (Category.id_comp f) = AlgHom.id k H) ∧
      (∀ (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f),
        ρ (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) = (ρ φ hφ).comp (ρ ψ hψ)) ∧
      (∀ (φ ψ χ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) (hχ : χ ≫ f = f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
            P.1 ≫ χ = (L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩
              ⟨P.1 ≫ ψ, by rw [Category.assoc, hψ]; exact P.2⟩).1) →
        ∀ x ∈ 𝒜 1, ρ χ hχ x = ρ φ hφ x + ρ ψ hψ x) ∧

      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f) (𝒱 : A.OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒦.ι)
          (hl : ∀ v, 𝒱.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam' v))
          (n : ℕ) (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 (n + 1)))),
          OModulePresheaf.unitPullback (πX := f) φ 𝒱 𝒦 lam hl (n + 1) z.1 -
              OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱 𝒦 lam' hl' (n + 1) z'.1 ∈
            LinearMap.range ((OModulePresheaf.unit f).d 𝒱 n) →
          ρ φ hφ (cls (n + 1) z) = cls (n + 1) z') ∧

      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f) (x : H),
          ρ₁ φ hφ (p₁ x) = p₁ (ρ φ hφ x) ∧ ρ₁ φ hφ (p₂ x) = p₂ x ∧
          ρ₂ φ hφ (p₁ x) = p₁ x ∧ ρ₂ φ hφ (p₂ x) = p₂ (ρ φ hφ x)) ∧

      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f) (𝒱 : (pullback f f).OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒲.ι)
          (hl : ∀ v, 𝒱.U v ≤
            (pullback.lift (pullback.fst f f ≫ φ) (pullback.snd f f)
              (by rw [Category.assoc, hφ]; exact pullback.condition)) ⁻¹ᵁ 𝒲.U (lam v))
          (hl' : ∀ v, 𝒱.U v ≤ (𝟙 (pullback f f)) ⁻¹ᵁ 𝒲.U (lam' v))
          (n : ℕ) (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (n + 1)))),
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f)
                (pullback.lift (pullback.fst f f ≫ φ) (pullback.snd f f)
                  (by rw [Category.assoc, hφ]; exact pullback.condition)) 𝒱 𝒲 lam hl (n + 1) z.1 -
              OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (𝟙 (pullback f f)) 𝒱 𝒲 lam' hl' (n + 1) z'.1 ∈
            LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒱 n) →
          ρ₁ φ hφ (cls' (n + 1) z) = cls' (n + 1) z') ∧
      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f) (𝒱 : (pullback f f).OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒲.ι)
          (hl : ∀ v, 𝒱.U v ≤
            (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ φ)
              (by rw [Category.assoc, hφ]; exact pullback.condition.trans rfl)) ⁻¹ᵁ 𝒲.U (lam v))
          (hl' : ∀ v, 𝒱.U v ≤ (𝟙 (pullback f f)) ⁻¹ᵁ 𝒲.U (lam' v))
          (n : ℕ) (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (n + 1)))),
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f)
                (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ φ)
                  (by rw [Category.assoc, hφ]; exact pullback.condition.trans rfl)) 𝒱 𝒲 lam hl (n + 1) z.1 -
              OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (𝟙 (pullback f f)) 𝒱 𝒲 lam' hl' (n + 1) z'.1 ∈
            LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒱 n) →
          ρ₂ φ hφ (cls' (n + 1) z) = cls' (n + 1) z') := by sorry
