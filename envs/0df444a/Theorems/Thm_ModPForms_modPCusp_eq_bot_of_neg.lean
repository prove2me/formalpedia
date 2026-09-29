-- Prove2me | Theorems.Thm_ModPForms_modPCusp_eq_bot_of_neg
-- name    : ModPForms.modPCusp_eq_bot_of_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/fe559037-5c50-5ffc-af42-a70c34bad265
-- title:
--   Mod p cusp forms of negative weight vanish
-- statement:
--   Let $N$ be a nonzero natural number, let $k$ be an integer with $k < 0$, and let $F$ be a field. The submodule $\mathrm{ModPForms.modPCusp}\ N\ k\ F$ of the formal power series ring $\mathrm{PowerSeries}\ F$ is by definition the $F$-span of the set of those power series $\varphi$ for which there exist a cusp form $f$ of weight $k$ on $\Gamma_0(N)$ and a sequence $a : \mathbb{N} \to \mathbb{Z}$ of integers such that the $n$-th $q$-expansion coefficient of $f$ (the $n$-th coefficient of `qExpansion 1 f`, i.e. the expansion of width $1$) equals the image of $a\,n$ in $\mathbb{C}$ for every $n$, and such that $\varphi$ is the power series whose $n$-th coefficient is the image of $a\,n$ in $F$. The assertion is that this submodule is the zero submodule $\bot$: for negative weight there are no nonzero reductions of integral $q$-expansions of cusp forms on $\Gamma_0(N)$, over any field $F$ whatsoever (no hypothesis relating the characteristic of $F$ to $N$ or $k$ is imposed).
--
--   This is the negative-weight vanishing statement for the spaces of reduced integral $q$-expansions of cusp forms used in the project, the cuspidal counterpart of the corresponding statement for the full space of forms. It is invoked in establishing that the power series attached to Hecke operators lie in these spaces, in [`ModPForms.heckePS_mem_modPCusp`](thm.html#ModPForms.heckePS_mem_modPCusp) and [`ModPForms.heckePS_mem_modPMod`](thm.html#ModPForms.heckePS_mem_modPMod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_modPCusp_eq_bot_of_neg.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.modPCusp_eq_bot_of_neg (N : ℕ) [NeZero N] (k : ℤ) (hk : k < 0) (F : Type) [Field F] :
    ModPForms.modPCusp N k F = ⊥ := by sorry
