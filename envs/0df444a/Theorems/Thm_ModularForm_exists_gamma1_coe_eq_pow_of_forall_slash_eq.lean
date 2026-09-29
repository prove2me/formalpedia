-- Prove2me | Theorems.Thm_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq
-- name    : ModularForm.exists_gamma1_coe_eq_pow_of_forall_slash_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/97493f68-647e-50c3-8d28-6dfb6af19080
-- title:
--   Powers of a Γ₀(M)-permuted family of Γ₁(M)-forms
-- statement:
--   Let $M$ be a nonzero natural number, $k$ an integer and $i$ a natural number, and let $F$ assign to each $t \in \mathbb{Z}/M$ a modular form $F_t$ of weight $k$ for the congruence subgroup $\Gamma_1(M)$, viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Assume that the family is permuted by $\Gamma_0(M)$ through the lower-right entry: for every $t \in \mathbb{Z}/M$ and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$, the weight-$k$ slash $F_t \mid_k \gamma$ equals, as a function on the upper half-plane, the function underlying $F_{t \cdot d_\gamma}$, where $d_\gamma$ is the reduction modulo $M$ of the $(1,1)$ entry of $\gamma$ (zero-indexed, i.e. the lower-right entry). The conclusion asserts the existence of a family $P$ assigning to each $t \in \mathbb{Z}/M$ a modular form of weight $i \cdot k$ for $\Gamma_1(M)$ such that, first, the function underlying $P_t$ is the $i$-th power of the function underlying $F_t$ for every $t$, and second, the family $P$ satisfies the same permutation identity in weight $i \cdot k$: $P_t \mid_{ik} \gamma = P_{t \cdot d_\gamma}$ as functions on the upper half-plane, for all $t \in \mathbb{Z}/M$ and all $\gamma \in \mathrm{SL}_2(\mathbb{Z}) \cap \Gamma_0(M)$.
--
--   This records that pointwise powers of a family of $\Gamma_1(M)$-modular forms permuted by the diamond action of $\Gamma_0(M)$ are again such a family, in the multiplied weight; it packages the graded-ring structure of modular forms together with the multiplicativity of the slash operator. It is used in the construction behind [`ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq`](thm.html#ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq), where products of such forms must be kept modular of the correct weight and equivariant for $\Gamma_0(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_gamma1_coe_eq_pow_of_forall_slash_eq
    (M : ℕ) [NeZero M] (k : ℤ) (i : ℕ)
    (F : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
      (⇑(F t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(F (t * ((γ 1 1 : ℤ) : ZMod M)))) :
    ∃ P : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) ((i : ℤ) * k),
      (∀ t : ZMod M, (⇑(P t) : UpperHalfPlane → ℂ) = (⇑(F t) : UpperHalfPlane → ℂ) ^ i) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(P t) : UpperHalfPlane → ℂ) ∣[(i : ℤ) * k] γ = ⇑(P (t * ((γ 1 1 : ℤ) : ZMod M)))) := by sorry
