-- Prove2me | Theorems.Thm_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem
-- name    : ModularCurve.diamondAutHBar_eq_refl_of_mem_or_neg_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/08386346-a508-558a-8b83-1264e74d31bd
-- title:
--   Triviality of ⟨ d⟩ on X_H(M) for d ∈ ± H
-- statement:
--   Let $M$ be a positive natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $d \in (\mathbb{Z}/M)^\times$ satisfy $d \in H$ or $-d \in H$. Then the diamond automorphism `diamondAutHBar M H d` of the field `xHFunctionFieldBar M H` — the base change to $\overline{\mathbb{Q}}$, inside $\overline{\mathbb{Q}}((q))$, of the function field `xHFunctionField M H` — is the identity $\overline{\mathbb{Q}}$-algebra automorphism. Here `diamondAutHBar M H d` is defined by choice: it is some $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of `xHFunctionFieldBar M H` with the property `IsDiamondAutHBar M H d σ` if such a $\sigma$ exists, and `AlgEquiv.refl` otherwise. The property `IsDiamondAutHBar M H d σ` asks that for every weight $k \in \mathbb{Z}$, all modular forms $f, g$ of weight $k$ on the group $\Gamma_H(M)$ viewed in $\mathrm{GL}(2,\mathbb{R})$, all integral $q$-expansions $p_f$ of $f$ and $p_g$ of $g$ with the associated Laurent series of $p_g$ nonzero, and every $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ lying in $\Gamma_0(M)$ whose upper-left entry reduces to $d$ modulo $M$, there is an element $y$ of `xHFunctionField M H` such that $\sigma$ sends the class of $p_f/p_g$ to the image of $y$ and such that, over $\mathbb{C}$, $y$ times the $q$-expansion of $g \mid_k \gamma$ equals the $q$-expansion of $f \mid_k \gamma$. Thus the assertion is that for $d \in \pm H$ the chosen automorphism is $\mathrm{id}$.
--
--   This is the statement that the diamond operator $\langle d \rangle$ acts trivially on the function field of $X_H(M)$ over $\overline{\mathbb{Q}}$ when $d$ or $-d$ lies in $H$, reflecting that $\Gamma_H(M)$ already contains a matrix in $\Gamma_0(M)$ with upper-left entry $d$ up to sign. It is used in the analysis of $q$-expansions of sections twisted by the Hecke correspondences on $X_H(M)$, namely in [`ModularCurve.exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist`](thm.html#ModularCurve.exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.diamondAutHBar_eq_refl_of_mem_or_neg_mem (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ) (hd : d ∈ H ∨ -d ∈ H) :
    ModularCurve.diamondAutHBar M H d = AlgEquiv.refl := by sorry
