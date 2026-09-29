-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_forall_affineOpens_coaction
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_forall_affineOpens_coaction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/a12bc96b-144a-512e-9af2-477fddfd44e9
-- title:
--   Primitives of H inject into degree-one Čech cohomology of mathcal O_A
-- statement:
--   Let $K$ be a field, let $f \colon A \to \operatorname{Spec} K$ be a morphism of schemes satisfying `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ carries a relative group law (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} K$, associative with unit and inverses, natural in $T$). Let $N \colon A \to A$ be a morphism with $N$ followed by $f$ equal to $f$, and let $H$ be a commutative ring with a Hopf $K$-algebra structure. Assume, with the $K$-algebra structures on all section rings induced from $f$, that there is a family of $K$-algebra maps $\rho_U \colon \Gamma(A, N^{-1}U) \to \Gamma(A, N^{-1}U) \otimes_K H$, indexed by the affine opens $U$ of $A$, such that: for affine opens $U, U'$ with $N^{-1}U' \le N^{-1}U$, the map $\rho$ commutes with restriction tensored with $\mathrm{id}_H$; each ring map $N^\ast \colon \Gamma(A,U) \to \Gamma(A, N^{-1}U)$ is injective; $\rho_U(N^\ast r) = N^\ast r \otimes 1$ for all $r$; every $s$ with $\rho_U(s) = s \otimes 1$ lies in the range of $N^\ast$; and every $h$ in [`primitives K H`](def/Dieudonne_ModpRealization.html#L16), the kernel of $\Delta - (\cdot \otimes 1) - (1 \otimes \cdot)$, admits $s$ with $\rho_U(s) = s \otimes 1 + 1 \otimes h$. Then for every ordered affine cover $\mathcal K$ of $A$ (a finite linearly ordered family of affine opens with supremum $\top$) there exists an injective $K$-linear map from the submodule of primitives of $H$ to $(\mathrm{OModulePresheaf.unit}\ f).\mathrm{HSucc}\ \mathcal K\ 0$, the degree-one Čech cohomology of $\mathcal K$ with coefficients in the presheaf $U \mapsto \Gamma(A,U)$, namely $\ker d^1$ modulo the image of $d^0$.
--
--   This is the Čech assembly step for additive characters: chartwise liftings of primitive elements, unique up to coinvariants, glue to a $1$-cocycle for the structure sheaf, giving an injection of the space of primitives of $H$ into $\check H^1(\mathcal K, \mathcal O_A)$. It is invoked in the variant [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear), and relies on the fact that global sections of an abelian scheme over a field are constants ([`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_algebraMap_sections_top`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_algebraMap_sections_top)) to identify coinvariant differences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_forall_affineOpens_coaction.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open TensorProduct

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_forall_affineOpens_coaction
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (N : A ⟶ A) (hN : N ≫ f = f)
    (H : Type u) [CommRing H] [HopfAlgebra K H]
    (hdata : letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
      ∃ ρ : (∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H),
        (∀ (U U' : A.affineOpens) (hle : (N ⁻¹ᵁ (U' : A.Opens)) ≤ N ⁻¹ᵁ (U : A.Opens))
            (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
            Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ρ U s) =
              ρ U' ((A.presheaf.map (homOfLE hle).op).hom s)) ∧
        (∀ U : A.affineOpens, Function.Injective (N.app (U : A.Opens)).hom) ∧
        (∀ (U : A.affineOpens) (r : Γ(A, (U : A.Opens))),
            ρ U ((N.app (U : A.Opens)).hom r) = (N.app (U : A.Opens)).hom r ⊗ₜ[K] (1 : H)) ∧
        (∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
            ρ U s = s ⊗ₜ[K] (1 : H) → s ∈ Set.range (N.app (U : A.Opens)).hom) ∧
        (∀ (U : A.affineOpens) (h : H), h ∈ primitives K H →
            ∃ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)), ρ U s = s ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] h))
    (𝒦 : A.OrderedAffineCover) :
    ∃ θ : ↥(primitives K H) →ₗ[K] (OModulePresheaf.unit f).HSucc 𝒦 0, Function.Injective θ := by sorry
