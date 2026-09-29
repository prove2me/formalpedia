-- Prove2me | Theorems.Thm_Module_nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff
-- name    : Module.nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/aad5ca85-d773-5df3-b439-e109c5f42957
-- title:
--   Cokernel of d^* is R/I under a kernel-lifting criterion
-- statement:
--   Let $R$ be a Noetherian commutative local ring with maximal ideal $\mathfrak m$ and residue field $k = R/\mathfrak m$, let $K_0$ and $K_1$ be finite free $R$-modules, and let $d : K_0 \to K_1$ be $R$-linear. Let $I$ be an ideal of $R$ with $I \subseteq \mathfrak m$ and $\mathfrak m^N \subseteq I$ for some $N \in \mathbb N$. Assume (U) that the kernel of the base-changed map $d \otimes k : k \otimes_R K_0 \to k \otimes_R K_1$ has dimension $1$ over $k$, and (W) that for every ideal $J'$ with $J' \subseteq \mathfrak m$ and $\mathfrak m^{N'} \subseteq J'$ for some $N' \in \mathbb N$, the following two conditions are equivalent: first, every $z \in k \otimes_R K_0$ killed by $d \otimes k$ is the image, under the map $(R/J') \otimes_R K_0 \to k \otimes_R K_0$ induced by the projection $R/J' \to R/\mathfrak m$, of some $w \in (R/J') \otimes_R K_0$ killed by $d \otimes (R/J')$; second, $I \subseteq J'$. The conclusion asserts that the type of $R$-linear isomorphisms $\operatorname{Hom}_R(K_0,R)/\operatorname{im}(d^{*}) \simeq R/I$ is nonempty, i.e. such an isomorphism exists, where $d^{*} : \operatorname{Hom}_R(K_1,R) \to \operatorname{Hom}_R(K_0,R)$ is the transpose of $d$.
--
--   This is the local-algebra pin identifying the cokernel $E$ of the transpose of $d$ with $R/I$: hypothesis (U) forces $E$ to be cyclic, and the lifting criterion (W) pins down its annihilator as $I$. It feeds the length-counting identity [`Module.toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient`](thm.html#Module.toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient), and relies on the natural identification of $\operatorname{Hom}_R(E,B)$ with $\ker(d \otimes B)$ recorded in [`Module.exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural`](thm.html#Module.exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (K₀ K₁ : Type u) [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Free R K₀]
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Free R K₁]
    (d : K₀ →ₗ[R] K₁)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (hIN : ∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ I)
    (hU : Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
      (LinearMap.ker (d.baseChange (R ⧸ IsLocalRing.maximalIdeal R))) = 1)
    (hW : ∀ (J' : Ideal R) (hJ' : J' ≤ IsLocalRing.maximalIdeal R), (∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ J') →
      ((∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K₀, d.baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
          ∃ w : (R ⧸ J') ⊗[R] K₀, d.baseChange (R ⧸ J') w = 0 ∧
            LinearMap.rTensor K₀ (Submodule.factor hJ') w = z) ↔ I ≤ J')) :
    Nonempty ((Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) ≃ₗ[R] (R ⧸ I)) := by sorry
