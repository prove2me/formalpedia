-- Prove2me | Theorems.Thm_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq
-- name    : ModularForm.exists_gammaH_coe_eq_of_forall_slash_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/1a4a3912-bc74-58ff-a2a2-5f1093cd06d3
-- title:
--   A Γ_H(M)-invariant form for Γ₁(M) is modular for Γ_H(M)
-- statement:
--   Let $M$ be a non-zero natural number, $H$ a subgroup of $(\mathbb{Z}/M)^\times$ and $k$ an integer. Write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ sending $\gamma$ to the unit with value $\gamma_{11} \bmod M$ and inverse $\gamma_{00} \bmod M$; concretely, the matrices of $\Gamma_0(M)$ whose lower-right entry reduces into $H$. Let $g$ be a modular form of weight $k$ for the image of $\Gamma_1(M)$ in $\mathrm{GL}_2(\mathbb{R})$, and assume that the underlying function $\mathfrak{H} \to \mathbb{C}$ of $g$ satisfies $g \mid_k \gamma = g$ for every $\gamma \in \Gamma_H(M)$, the slash action being taken through the inclusion of $\mathrm{SL}_2(\mathbb{Z})$. Then there exists a modular form $f$ of weight $k$ for the image of $\Gamma_H(M)$ in $\mathrm{GL}_2(\mathbb{R})$ whose underlying function $\mathfrak{H} \to \mathbb{C}$ is equal to that of $g$.
--
--   This is the change-of-level statement for the intermediate groups $\Gamma_1(M) \le \Gamma_H(M) \le \Gamma_0(M)$: an element of $M_k(\Gamma_1(M))$ that happens to be invariant under the diamond operators indexed by $H$ is an element of $M_k(\Gamma_H(M))$, with no change of the function. It is used in the decomposition of $\Gamma_1(M)$-forms along the groups $\Gamma_H(M)$, via [`ModularForm.exists_gammaH_coe_eq_sum_of_forall_slash_eq`](thm.html#ModularForm.exists_gammaH_coe_eq_sum_of_forall_slash_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq.lean

import Mathlib
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_gammaH_coe_eq_of_forall_slash_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hg : ∀ γ ∈ CohCarrier.GammaH M H, (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = ⇑g) :
    ∃ f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑f : UpperHalfPlane → ℂ) = ⇑g := by sorry
