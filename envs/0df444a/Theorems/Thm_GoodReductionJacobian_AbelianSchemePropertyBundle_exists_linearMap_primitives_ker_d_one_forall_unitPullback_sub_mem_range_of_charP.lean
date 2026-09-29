-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_ker_d_one_forall_unitPullback_sub_mem_range_of_charP
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_ker_d_one_forall_unitPullback_sub_mem_range_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/28894722-7dcb-5bad-aab5-3870cde9bf14
-- title:
--   Equivariant Čech realisation of the primitives of A[p]
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$, $p$ prime, and let $f : A \to \operatorname{Spec} K$ be a morphism of schemes equipped with a relative group law $L$ (functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points over $K$-schemes, natural in $T$) which is commutative, and satisfying `AbelianSchemePropertyBundle`: $f$ is smooth and proper, every fibre of $f$ is connected, and $f$ carries a relative group law; assume further $f$ smooth of relative dimension $g$. Let $H$ be a commutative, finite-dimensional, cocommutative Hopf $K$-algebra with $\dim_K H = p^{2g}$ whose $p$-th convolution power of the identity is $\eta \circ \varepsilon$, and suppose given, for every commutative $K$-algebra $T$, a bijection $e_T$ from the convolution monoid of $K$-algebra maps $H \to T$ onto the set of $p$-torsion points of $L$ over $\operatorname{Spec} T$, compatible with the products (`he_mul`) and natural in $T$ (`he_nat`). Let $\mathcal K$ be an ordered affine cover of $A$: a finite, linearly ordered family of affine opens with supremum $\top$. Then there is a $K$-linear map $\theta$ from the primitives of $H$, i.e. the kernel of $\Delta - (\cdot \otimes 1) - (1 \otimes \cdot)$, into the kernel of the degree-one Čech differential $d^1$ of the presheaf of $K$-modules `OModulePresheaf.unit f` (the structure sheaf of $A$) on $\mathcal K$, such that: (i) $\theta x$ is a coboundary only for $x = 0$; (ii) every $1$-cocycle differs from some $\theta x$ by an element of the image of $d^0$; and (iii) for every $\varphi : A \to A$ with $\varphi \circ f = f$ that is additive on points (for all $t : T \to \operatorname{Spec} K$ and points $P, Q$ over $t$, the composite of $L.\mathrm{mul}\,t\,P\,Q$ with $\varphi$ is $L.\mathrm{mul}\,t$ applied to $P$ followed by $\varphi$ and $Q$ followed by $\varphi$) there is a $K$-algebra map $\varphi_H : H \to H$ with $e_T(q \circ \varphi_H)$ equal to $e_T(q)$ followed by $\varphi$ for all $T$ and all $q$, preserving the primitives, and such that for every ordered affine cover $\mathcal W$ of $A$, all index maps $\lambda, \lambda' : \mathcal W.\iota \to \mathcal K.\iota$ with $\mathcal W.U\,w \le \varphi^{-1}(\mathcal K.U(\lambda w))$ and $\mathcal W.U\,w \le \mathrm{id}^{-1}(\mathcal K.U(\lambda' w))$, and all primitives $x, y$ with $\varphi_H x = y$, the difference of the signed cochain pullbacks `OModulePresheaf.unitPullback` of $\theta x$ along $\varphi$ and of $\theta y$ along $\mathbf 1_A$ lies in the image of $d^0$ for $\mathcal W$.
--
--   This is the Čech-level form of the identification of $\operatorname{Hom}(A[p], \mathbb G_a)$, realised as the primitives of the Hopf algebra of $A[p]$, with $\check H^1(A, \mathcal O_A)$ for an abelian variety in characteristic $p$, made equivariant for endomorphisms of $A$ that are homomorphisms on points. It is used in the computation of the rank and of the trace of the induced action on $\check H^1$ in the study of fake elliptic curves over fields of characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_ker_d_one_forall_unitPullback_sub_mem_range_of_charP.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_ker_d_one_forall_unitPullback_sub_mem_range_of_charP
    (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]

    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (hH : Module.finrank K H = p ^ (2 * g))
    (hHp : PDivisibleGroup.Hopf.nsmulAlgHom K H p = (Algebra.ofId K H).comp (Bialgebra.counitAlgHom K H))
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) p)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    (𝒦 : A.OrderedAffineCover) :
    ∃ θ : ↥(primitives K H) →ₗ[K] ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1)),

      (∀ x : ↥(primitives K H),
        ((θ x : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1))) : (OModulePresheaf.unit f).cochain 𝒦 1) ∈
          LinearMap.range ((OModulePresheaf.unit f).d 𝒦 0) → x = 0) ∧

      (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1)), ∃ x : ↥(primitives K H),
        (z : (OModulePresheaf.unit f).cochain 𝒦 1) - (θ x : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1))).1 ∈
          LinearMap.range ((OModulePresheaf.unit f).d 𝒦 0)) ∧

      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
            (L.mul t P Q).1 ≫ φ =
              (L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩ ⟨Q.1 ≫ φ, by rw [Category.assoc, hφ]; exact Q.2⟩).1) →

        ∃ φH : H →ₐ[K] H,
          (∀ (T : Type u) [CommRing T] [Algebra K T] (q : WithConv (H →ₐ[K] T)),
            ((e T (.toConv (q.ofConv.comp φH))).val : SchemeHomOver _ f).1 = (e T q).val.1 ≫ φ) ∧
          (∀ x ∈ primitives K H, φH x ∈ primitives K H) ∧

          (∀ (𝒲 : A.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
            (hlam : ∀ w, 𝒲.U w ≤ φ ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam' w))
            (x y : ↥(primitives K H)), φH x = y →
            OModulePresheaf.unitPullback (πX := f) φ 𝒲 𝒦 lam hlam 1
                (θ x : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1))).1 -
              OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam' hlam' 1
                (θ y : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1))).1 ∈
            LinearMap.range ((OModulePresheaf.unit f).d 𝒲 0))) := by sorry
