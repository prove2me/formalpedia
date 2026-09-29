-- Prove2me | Theorems.Thm_ModPForms_modPMod_eq_bot_of_neg
-- name    : ModPForms.modPMod_eq_bot_of_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/957228f2-ac62-591c-b008-c790a014fad1
-- title:
--   Vanishing of mod-p forms of negative weight
-- statement:
--   Let $N$ be a natural number, assumed nonzero, let $k$ be an integer with $k < 0$, and let $F$ be a field. Consider the set of formal power series $\varphi \in F[[q]]$ for which there exist a modular form $f$ of weight $k$ on $\mathrm{Gamma0}(N)$ and a sequence of integers $a : \mathbb{N} \to \mathbb{Z}$ such that the $n$-th coefficient of the level-one $q$-expansion of $f$ equals $a_n$ viewed in $\mathbb{C}$ for every $n$, and such that $\varphi$ is the power series whose $n$-th coefficient is the image of $a_n$ in $F$; the $F$-submodule of $F[[q]]$ spanned by this set is denoted [`ModPForms.modPMod N k F`](def/CuspForm_ModPForms.html#L12). The theorem asserts that this submodule is the zero submodule $\bot$. In other words, the $F$-span of the reductions of the integral $q$-expansions of weight-$k$ forms on $\mathrm{Gamma0}(N)$ vanishes when $k$ is negative.
--
--   This is the negative-weight slice of the mod-$p$ (more generally, mod-$F$) theory of $q$-expansions of forms on $\mathrm{Gamma0}(N)$: there are no nonzero modular forms of negative weight on a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$, so the associated space of reductions is zero. It is used in the filtration statements for these spaces, where multiplication by a form raises the weight, by [`ModPForms.heckePS_mem_modPCusp`](thm.html#ModPForms.heckePS_mem_modPCusp), [`ModPForms.heckePS_mem_modPMod`](thm.html#ModPForms.heckePS_mem_modPMod) and [`ModPForms.mem_modPMod_sub_of_qP_mul_mem`](thm.html#ModPForms.mem_modPMod_sub_of_qP_mul_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_modPMod_eq_bot_of_neg.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.modPMod_eq_bot_of_neg (N : ℕ) [NeZero N] (k : ℤ) (hk : k < 0) (F : Type) [Field F] :
    ModPForms.modPMod N k F = ⊥ := by sorry
