-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_gradedMonoid_kunneth_injective_cech_unit
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_gradedMonoid_kunneth_injective_cech_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/28daea9d-8eb8-5ce0-b46d-ac5728f9a8a6
-- title:
--   Graded Čech algebra of an abelian scheme and Künneth injectivity
-- statement:
--   Let $k$ be a field, let $A$ be a scheme and $f \colon A \to \operatorname{Spec} k$ a morphism carrying a `RelativeGroupLaw` $L$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, with multiplication, unit, inverse, the group axioms and naturality in $T$), and assume `AbelianSchemePropertyBundle k f`: $f$ is smooth, proper, has connected fibres, and admits a relative group law. Let $\mathcal K$ be an ordered affine cover of $A$ (a finite linearly ordered index set, affine opens whose supremum is $\top$) and $\mathcal W$ one of $A \times_{\operatorname{Spec} k} A$, together with index maps $\lambda_1, \lambda_2, \lambda_3$ such that each $\mathcal W_w$ lies in the preimage of $\mathcal K_{\lambda_1 w}$ under the first projection, of $\mathcal K_{\lambda_2 w}$ under the second, and of $\mathcal K_{\lambda_3 w}$ under the morphism $\mu$ obtained by applying $L.\mathrm{mul}$ over the base morphism $\mathrm{fst} \circ f$ to the two projections viewed as points over that base. Then there exist $k$-algebras $H$ and $H'$, $k$-submodules $\mathcal A_n \subseteq H$ ($n \in \mathbb N$) forming a graded monoid ($1 \in \mathcal A_0$, $\mathcal A_a \mathcal A_b \subseteq \mathcal A_{a+b}$), $k$-algebra maps $p_1, p_2, m \colon H \to H'$, and $k$-linear maps $\mathrm{cls}_n$ from the kernel of the degree-$n$ Čech differential of the presheaf $U \mapsto \Gamma(A,U)$ on $\mathcal K$ (cochains being families of sections over the intersections indexed by strictly increasing tuples) to $H$, and $\mathrm{cls}'_n$ from the corresponding kernel for $U \mapsto \Gamma(A\times A, U)$ on $\mathcal W$ (over the base morphism $\mathrm{fst} \circ f$) to $H'$, such that: the image of $\mathrm{cls}_n$ is exactly $\mathcal A_n$; $\mathrm{cls}_0 z = 0$ iff $z = 0$ and $\mathrm{cls}_{n+1} z = 0$ iff $z$ lies in the image of the degree-$n$ differential, and likewise for $\mathrm{cls}'$; the map $\bigoplus_{(a,b)\in\mathbb N\times\mathbb N} \mathcal A_a \otimes_k \mathcal A_b \to H'$, $x \otimes y \mapsto p_1(x)\,p_2(y)$, is injective; $p_2(x)p_1(y) = (-1)^{ab}\,p_1(y)p_2(x)$ for $x \in \mathcal A_a$, $y \in \mathcal A_b$; $m(x) = p_1(x) + p_2(x)$ for $x \in \mathcal A_1$; and for every $n$ and every cocycle $z$ in degree $n$ the three `unitPullback` cochains of $z$ along the two projections and along $\mu$ (formed with $\lambda_1,\lambda_2,\lambda_3$ and the inclusion hypotheses, by signed restriction of the pullback section at the sorted index tuple, zero on degenerate tuples) are again cocycles, and their $\mathrm{cls}'_n$-classes are $p_1(\mathrm{cls}_n z)$, $p_2(\mathrm{cls}_n z)$ and $m(\mathrm{cls}_n z)$ respectively.
--
--   This packages the alternating Čech cohomology of the structure sheaf of an abelian scheme over a field as a graded $k$-algebra, together with the comparison maps to the square $A \times_k A$ induced by the two projections and by the group law, the Künneth injectivity of $x \otimes y \mapsto p_1(x)p_2(y)$, graded commutation of the two factors, and primitivity of degree-one classes, in the form used downstream. It is cited in the computation of the dimension of $\check H^1(\mathcal K, \mathcal O_A)$ in characteristic $p$ and in the construction of point derivations from the degree-two obstruction cocycle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_gradedMonoid_kunneth_injective_cech_unit.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_gradedMonoid_kunneth_injective_cech_unit
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
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
      (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)) →ₗ[k] H'),

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
          p₁ (cls n z) = cls' n ⟨_, hz₁⟩ ∧ p₂ (cls n z) = cls' n ⟨_, hz₂⟩ ∧ m (cls n z) = cls' n ⟨_, hz₃⟩) := by sorry
