-- Prove2me | Theorems.Thm_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq
-- name    : ModularForm.exists_gammaH_coe_eq_sum_of_forall_slash_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/8db9a702-ce8a-5744-92ed-311516dba921
-- title:
--   H-symmetrisation of a Γ₀(M)-permuted family of Γ₁(M)-forms
-- statement:
--   Let $M$ be a nonzero natural number, $H$ a subgroup of $(\mathbb{Z}/M)^\times$ with finitely many elements, and $k$ an integer. Let $F$ be a family, indexed by $t \in \mathbb{Z}/M$, of weight-$k$ modular forms for the image of $\Gamma_1(M)$ in $\mathrm{GL}_2(\mathbb{R})$, and assume the permutation law: for every $t \in \mathbb{Z}/M$ and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$, the underlying function of $F_t$ slashed in weight $k$ by $\gamma$ equals the underlying function of $F_{t\,\bar d}$, where $\bar d$ is the reduction modulo $M$ of the lower-right entry $\gamma_{11}$. The conclusion asserts the existence of a family $V$, indexed by $t \in \mathbb{Z}/M$, of weight-$k$ modular forms for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{GL}_2(\mathbb{R})$ — the group of those $\gamma \in \Gamma_0(M)$ whose associated unit of $\mathbb{Z}/M$ (with value the reduction of $\gamma_{11}$ and inverse the reduction of $\gamma_{00}$) lies in $H$ — such that, as functions on the upper half-plane, $V_t = \sum_{h \in H} F_{th}$ for all $t$, and such that $V$ again satisfies the same permutation law $V_t \mid_k \gamma = V_{t\,\bar d}$ for all $t$ and all $\gamma \in \Gamma_0(M)$.
--
--   This is the passage from a $\Gamma_0(M)$-permuted family of $\Gamma_1(M)$-forms to its averages over the diamond operators indexed by $H$, which are modular forms for $\Gamma_H(M)$ while retaining the permutation law. It is used in the construction of forms on $\Gamma_H(M)$ separating prescribed values, in [`ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq`](thm.html#ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq.lean

import Mathlib
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_gammaH_coe_eq_sum_of_forall_slash_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) [Fintype H] (k : ℤ)
    (F : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
      (⇑(F t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(F (t * ((γ 1 1 : ℤ) : ZMod M)))) :
    ∃ V : ZMod M → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ t : ZMod M, (⇑(V t) : UpperHalfPlane → ℂ) =
        ∑ h : H, (⇑(F (t * ((h : (ZMod M)ˣ) : ZMod M))) : UpperHalfPlane → ℂ)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(V t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(V (t * ((γ 1 1 : ℤ) : ZMod M)))) := by sorry
