-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/b96e867a-47f6-5f16-aa56-9aaab9d8b80a
-- title:
--   Čech-level primitivity of 1-cocycles on A× A
-- statement:
--   Let $k$ be a field and $f \colon A \to \operatorname{Spec} k$ a morphism of schemes equipped with a relative group law $L$ (functorial multiplication, unit and inversion on $T$-points over $\operatorname{Spec} k$, satisfying associativity, the unit laws, left inversion and naturality in $T$) and with the bundle of properties `AbelianSchemePropertyBundle`, namely that $f$ is smooth and proper, each fibre of $f$ over a point of $\operatorname{Spec} k$ is connected, and a relative group law exists. Let $\mathcal K$ be an ordered affine cover of $A$ (a finite, linearly ordered family of affine opens with supremum $\top$) and $\mathcal W$ one of $P = \operatorname{pullback} f f = A \times_k A$. Let $\lambda_1,\lambda_2,\lambda_3 \colon \mathcal W.\iota \to \mathcal K.\iota$ be index maps such that each $\mathcal W.U(w)$ lies in the preimage of $\mathcal K.U(\lambda_1 w)$ under the first projection $p_1$, in the preimage of $\mathcal K.U(\lambda_2 w)$ under the second projection $p_2$, and in the preimage of $\mathcal K.U(\lambda_3 w)$ under $\mu := L.\mathrm{mul}$ applied, over the base morphism $p_1 \circ f$, to the two tautological points $p_1$ and $p_2$ of $A$. Finally let $z$ be a degree-$1$ Čech cochain for the presheaf `OModulePresheaf.unit f` on $\mathcal K$ (a section of $\mathcal O_A$ on each intersection $\bigcap_j \mathcal K.U(s_j)$ indexed by the degree-$1$ indices $s$ of $\mathcal K$) with $d^1 z = 0$. The assertion is that there exists a degree-$0$ cochain $b$ for `OModulePresheaf.unit` $(p_1 \circ f)$ on $\mathcal W$ with $$d^0 b = \mu^*_{\lambda_3} z - p_1^*{}_{\lambda_1} z - p_2^*{}_{\lambda_2} z,$$ where each term is the cochain pullback `OModulePresheaf.unitPullback` along the indicated morphism with the indicated index map, whose value at a simplex $s$ of $\mathcal W$ is, when $\lambda \circ s$ is injective, the sign of the sorting permutation times the restriction of the pullback of $z$ at the sorted index, and is $0$ otherwise.
--
--   This is the Čech-cochain form of the classical primitivity relation $\mu^* = p_1^* + p_2^*$ on $H^1(A,\mathcal O_A)$ for an abelian variety, asserting that the difference of the three pullbacks of a $1$-cocycle is a coboundary on $A \times_k A$. It feeds the companion relation for the inversion morphism and the Künneth-injectivity statements about cup products of Čech classes for the structure sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝒦 : A.OrderedAffineCover)
    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w))
    (h₃ : ∀ w, 𝒲.U w ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ 𝒦.U (lam₃ w))
    (z : (OModulePresheaf.unit f).cochain 𝒦 1) (hz : (OModulePresheaf.unit f).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 0,
      (OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 𝒲 𝒦 lam₃ h₃ 1 z -
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ 1 z -
          OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ 1 z := by sorry
