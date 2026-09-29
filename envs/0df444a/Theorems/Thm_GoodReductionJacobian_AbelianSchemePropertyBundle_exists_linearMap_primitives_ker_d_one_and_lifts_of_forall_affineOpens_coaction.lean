-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_ker_d_one_and_lifts_of_forall_affineOpens_coaction
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_ker_d_one_and_lifts_of_forall_affineOpens_coaction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/0c01548c-f239-51dd-87bf-083fac059efc
-- title:
--   Pinned cocycle map from primitives to degree-one Čech cocycles
-- statement:
--   Let $K$ be a field, let $f : A \to \operatorname{Spec} K$ be a scheme morphism satisfying `AbelianSchemePropertyBundle` (that is, $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists), let $N : A \to A$ satisfy $N$ followed by $f$ equals $f$, and let $H$ be a commutative Hopf $K$-algebra; every $\Gamma(A,V)$ carries the $K$-algebra structure induced by $f$. Consider a family $\rho_U : \Gamma(A, N^{-1}U) \to \Gamma(A, N^{-1}U) \otimes_K H$ of $K$-algebra maps indexed by the affine opens $U$ of $A$, subject to: compatibility with restriction, in the sense that for $N^{-1}U' \le N^{-1}U$ the map $\mathrm{res} \otimes \mathrm{id}$ carries $\rho_U(s)$ to $\rho_{U'}(s|_{N^{-1}U'})$; injectivity of $N^{*} = N^{\sharp}_U$ on $\Gamma(A,U)$ for each affine $U$; invariance $\rho_U(N^{*}r) = N^{*}r \otimes 1$; the converse, that any $s$ with $\rho_U(s) = s \otimes 1$ lies in the range of $N^{*}$; and local liftability, that for every $h$ in $\mathrm{primitives}\,K\,H$ (the kernel of $\Delta - (x \mapsto x \otimes 1) - (x \mapsto 1 \otimes x)$) and every affine $U$ there is $s$ with $\rho_U(s) = s \otimes 1 + 1 \otimes h$. Let $\mathcal K$ be an ordered affine cover of $A$: a finite linearly ordered index type $\iota$ with affine opens $U_i$ whose supremum is $\top$. Then there exist a $K$-linear map $\theta$ from the submodule of primitives of $H$ into the kernel of the degree-one Čech differential of the presheaf $U \mapsto \Gamma(A,U)$ on $\mathcal K$, and a family of sections $s(x)_i \in \Gamma(A, N^{-1}U_i)$, such that: (a) $\rho_{U_i}(s(x)_i) = s(x)_i \otimes 1 + 1 \otimes x$ for all primitives $x$ and all $i$; (b) for every strictly increasing pair $t = (t_0 < t_1)$ in $\iota$, $N^{*}\bigl(\theta(x)_t\bigr)$ equals the difference of the restrictions of $s(x)_{t_0}$ and $s(x)_{t_1}$ to $N^{-1}(U_{t_0} \cap U_{t_1})$; and (c) if the cochain $\theta(x)$ lies in the range of the degree-zero differential, then $x = 0$.
--
--   This is the boundary map sending a primitive element of $H$ to the class of the $N$-descent obstruction of its local lifts, realised concretely as a $1$-cocycle for an ordered affine cover together with the chartwise lifts that produce it; condition (c) says that the induced map to $H^1(\mathcal K, \mathcal O_A)$ is injective. The pinning data (a) and (b) are what allow the cocycle on one cover to be compared with pulled-back lifts on a refinement; the statement feeds into [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_ker_d_one_forall_unitPullback_sub_mem_range_of_charP`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_ker_d_one_forall_unitPullback_sub_mem_range_of_charP). The proof cites only the fact that the global sections of such an $f$ are the constants $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_ker_d_one_and_lifts_of_forall_affineOpens_coaction.lean

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
open scoped TensorProduct

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_ker_d_one_and_lifts_of_forall_affineOpens_coaction
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (N : A ⟶ A) (hN : N ≫ f = f)
    (H : Type u) [CommRing H] [HopfAlgebra K H] :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    ∀ (ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
      (hnat : ∀ (U U' : A.affineOpens) (hle : (N ⁻¹ᵁ (U' : A.Opens)) ≤ N ⁻¹ᵁ (U : A.Opens))
          (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ρ U s) =
            ρ U' ((A.presheaf.map (homOfLE hle).op).hom s))
      (hinj : ∀ U : A.affineOpens, Function.Injective (N.app (U : A.Opens)).hom)
      (hρN : ∀ (U : A.affineOpens) (r : Γ(A, (U : A.Opens))),
          ρ U ((N.app (U : A.Opens)).hom r) = (N.app (U : A.Opens)).hom r ⊗ₜ[K] (1 : H))
      (hcoinv : ∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
          ρ U s = s ⊗ₜ[K] (1 : H) → s ∈ Set.range (N.app (U : A.Opens)).hom)
      (hlift : ∀ (U : A.affineOpens) (h : H), h ∈ primitives K H →
          ∃ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)), ρ U s = s ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] h)
      (𝒦 : A.OrderedAffineCover),
    ∃ (θ : ↥(primitives K H) →ₗ[K] ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1)))
      (s : ↥(primitives K H) → ∀ i : 𝒦.ι, Γ(A, N ⁻¹ᵁ 𝒦.U i)),

      (∀ (x : ↥(primitives K H)) (i : 𝒦.ι),
        ρ ⟨𝒦.U i, 𝒦.isAffineOpen i⟩ (s x i) = s x i ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒦.U i)) ⊗ₜ[K] (x : H)) ∧

      (∀ (x : ↥(primitives K H)) (t : 𝒦.Idx 1),
        (N.app (𝒦.inter t)).hom
            ((θ x : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1))).1 t) =
          (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 0))).op).hom (s x (t.1 0)) -
            (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 1))).op).hom (s x (t.1 1))) ∧

      (∀ x : ↥(primitives K H),
        ((θ x : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1))) : (OModulePresheaf.unit f).cochain 𝒦 1) ∈
          LinearMap.range ((OModulePresheaf.unit f).d 𝒦 0) → x = 0) := by sorry
