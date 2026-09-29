-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/00a35bd6-754b-5d29-a87f-234c907f49b5
-- title:
--   Inversion acts as -1 on Čech 1-cocycles of 𝒪_A
-- statement:
--   Let $k$ be a field and $f \colon A \to \operatorname{Spec} k$ a morphism of schemes, equipped with a `RelativeGroupLaw` $L$ over $k$ (a functorial group structure on the sets $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of $T$-points, natural in $T$), and assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists. Let $\mathcal{K}$ and $\mathcal{W}$ be ordered affine covers of $A$, that is, finite linearly ordered index sets together with affine opens whose supremum is $\top$. Write $\iota = (L.\mathrm{inv}\,f\,\langle \mathrm{id}_A\rangle).1 \colon A \to A$ for the underlying morphism of the inverse of the identity $A$-point. Let $\lambda_1, \lambda_2 \colon \mathcal{W}.\iota \to \mathcal{K}.\iota$ be refinement maps with $\mathcal{W}.U(w) \le \iota^{-1}(\mathcal{K}.U(\lambda_1 w))$ and $\mathcal{W}.U(w) \le \mathrm{id}_A^{-1}(\mathcal{K}.U(\lambda_2 w))$ for all $w$. Then for every $1$-cochain $z$ of the structure presheaf $U \mapsto \Gamma(A,U)$ on $\mathcal{K}$ with $dz = 0$ there is a $0$-cochain $b$ on $\mathcal{W}$ whose coboundary equals the sum of the signed `unitPullback` of $z$ along $\iota$ via $\lambda_1$ and along $\mathrm{id}_A$ via $\lambda_2$.
--
--   This is the cochain-level form of the statement that the inversion morphism of an abelian variety acts as $-1$ on $H^1(A, \mathcal{O}_A)$: the two pullbacks of a $1$-cocycle add up to a coboundary on a suitable refinement. It is used in the construction of the comparison isomorphisms for the unit presheaf cohomology that enter the Jacobian good-reduction package, via the two results on isomorphisms of $H^1$ that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero.lean

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

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝒦 𝒲 : A.OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₂ w))
    (z : (OModulePresheaf.unit f).cochain 𝒦 1) (hz : (OModulePresheaf.unit f).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit f).cochain 𝒲 0,
      (OModulePresheaf.unit f).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := f) (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 𝒲 𝒦 lam₁ h₁ 1 z +
          OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam₂ h₂ 1 z := by sorry
