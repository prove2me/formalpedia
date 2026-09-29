-- Prove2me | Theorems.Thm_ModPForms_modPMod_eq_bot_of_odd
-- name    : ModPForms.modPMod_eq_bot_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/affd00bd-51e0-558c-ba13-3ba003da6cd9
-- title:
--   Vanishing of the mod-p forms of odd weight on Γ₀(N)
-- statement:
--   Let $N$ be a natural number, $k$ an integer which is odd, and $F$ a field. Consider the $F$-submodule [`ModPForms.modPMod N k F`](def/CuspForm_ModPForms.html#L12) of the formal power series ring $F[[q]]$, defined as the $F$-span of the set of those power series $\varphi$ for which there exist a modular form $f$ of weight $k$ on the congruence subgroup $\Gamma_0(N)$ and a function $a \colon \mathbb{N} \to \mathbb{Z}$ such that the $n$-th coefficient of the $q$-expansion of $f$ at the cusp $\infty$ (taken with width $1$, i.e. [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19)) equals the image of $a(n)$ in $\mathbb{C}$ for every $n$, and $\varphi$ is the power series whose $n$-th coefficient is the image of $a(n)$ in $F$. The assertion is that this submodule is the zero submodule $\bot$. No hypothesis is imposed on $N$, on the characteristic of $F$, or on the sign or size of $k$ beyond its parity.
--
--   This records that $\Gamma_0(N)$, containing $-1$, carries no nonzero modular forms of odd weight, so the spaces of integral $q$-expansion reductions in odd weight are trivial; it allows the weight bookkeeping for mod-$p$ forms to be carried out on even weights only. It is used in the arguments about membership in `modPMod` in shifted weights, namely [`ModPForms.mem_modPMod_sub_of_qP_mul_mem`](thm.html#ModPForms.mem_modPMod_sub_of_qP_mul_mem), [`ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed`](thm.html#ModPForms.mem_modPMod_sub_two_of_ladder_mul_mem_modPMod_add_two_of_not_three_dvd_of_dvd_of_mod_three_eq_two_of_isAlgClosed) and [`ModularCurve.SSHeckeV2.mem_modPMod_sub_of_resQFun_eq_zero`](thm.html#ModularCurve.SSHeckeV2.mem_modPMod_sub_of_resQFun_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_modPMod_eq_bot_of_odd.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.modPMod_eq_bot_of_odd (N : ℕ) (k : ℤ) (hk : Odd k) (F : Type) [Field F] :
    ModPForms.modPMod N k F = ⊥ := by sorry
