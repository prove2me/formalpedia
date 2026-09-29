-- Prove2me | Theorems.Thm_ModPForms_finiteDimensional_modPMod
-- name    : ModPForms.finiteDimensional_modPMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/e0431c4b-8b24-5221-8690-d2287c4d9452
-- title:
--   Finite-dimensionality of the mod-p forms M_k(N;F)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, let $k$ be an integer, and let $F$ be a field. Consider the $F$-submodule [`ModPForms.modPMod N k F`](def/CuspForm_ModPForms.html#L12) of the formal power series ring $F[[q]]$ defined as the $F$-span of the set of those $\varphi$ for which there exist a modular form $f$ of weight $k$ on the congruence subgroup $\Gamma_0(N)$ (viewed inside $\mathrm{GL}_2(\mathbb{R})$) and a sequence of integers $(a_n)_{n \in \mathbb{N}}$ such that the $n$-th coefficient of the $q$-expansion of $f$ with respect to the period $1$ equals $a_n$ for every $n$, and $\varphi = \sum_n \bar{a}_n q^n$ is the power series whose $n$-th coefficient is the image of $a_n$ in $F$. The assertion is that this submodule is finite-dimensional as an $F$-vector space. No hypothesis is imposed on the characteristic of $F$, and no bound on the dimension is asserted.
--
--   This is the finiteness statement for spaces of mod-$p$ modular forms obtained by reducing integral $q$-expansions of forms on $\Gamma_0(N)$, in the style of Serre and Swinnerton-Dyer. It underlies the later existence results producing elements of [`ModPForms.modPMod`](def/CuspForm_ModPForms.html#L12) with prescribed $q$-expansions, and the comparison of this span with the corresponding space of cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_finiteDimensional_modPMod.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.finiteDimensional_modPMod (N : ℕ) [NeZero N] (k : ℤ) (F : Type) [Field F] :
    FiniteDimensional F ↥(ModPForms.modPMod N k F) := by sorry
