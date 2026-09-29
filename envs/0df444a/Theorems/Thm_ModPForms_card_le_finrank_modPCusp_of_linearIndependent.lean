-- Prove2me | Theorems.Thm_ModPForms_card_le_finrank_modPCusp_of_linearIndependent
-- name    : ModPForms.card_le_finrank_modPCusp_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/f44e9ffc-b6e0-5089-8cc3-37552b10d07d
-- title:
--   Integral cusp forms: reduction preserves rank
-- statement:
--   Let $N$ be a nonzero natural number, $k$ an integer, and $F$ an arbitrary field. Let $\iota$ be a finite index type, let $f : \iota \to \mathrm{CuspForm}(\Gamma_0(N), k)$ be a family of cusp forms of weight $k$ for the congruence subgroup $\Gamma_0(N)$ (taken inside $\mathrm{GL}_2(\mathbb{R})$), and let $a : \iota \to \mathbb{N} \to \mathbb{Z}$ be integers such that for every $i$ and every $n$ the $n$-th coefficient of the $q$-expansion of $f_i$ of width $1$, namely [`ModularFormClass.qCoeff (f i) n`](def/FLTPrelim_Modularity.html#L19), equals the image of $a_i(n)$ in $\mathbb{C}$; thus each $f_i$ has integral $q$-expansion with coefficients $a_i$. Assume the family $f$ is linearly independent over $\mathbb{C}$. The conclusion is that the cardinality of $\iota$ is at most $\dim_F$ of [`ModPForms.modPCusp N k F`](def/CuspForm_ModPForms.html#L7), the $F$-submodule of the formal power series ring $F[[q]]$ spanned by all series $\sum_n \bar{b}(n) q^n$ arising from some cusp form $g$ of weight $k$ for $\Gamma_0(N)$ and some integer sequence $b$ with [`ModularFormClass.qCoeff g n`](def/FLTPrelim_Modularity.html#L19) $= b(n)$ in $\mathbb{C}$ for all $n$, the coefficients being reduced into $F$. No condition relating the characteristic of $F$ to $N$ or $k$ is imposed.
--
--   This is the cuspidal form of the statement that coefficientwise reduction of integral $q$-expansions does not lose rank: a $\mathbb{C}$-independent family of integral cusp forms of weight $k$ on $\Gamma_0(N)$ forces the reduced space $\widetilde{S}_k(N;F)$ to have $F$-dimension at least as large. It feeds the comparison of the complex cuspidal dimension with $\dim_F$ of the mod-$p$ cuspidal space and the rank estimate for the kernel of the $U$-operator in weight two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_card_le_finrank_modPCusp_of_linearIndependent.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.card_le_finrank_modPCusp_of_linearIndependent
    (N : ℕ) [NeZero N] (k : ℤ) (F : Type) [Field F] {ι : Type} [Fintype ι]
    (f : ι → CuspForm (CongruenceSubgroup.Gamma0 N) k) (a : ι → ℕ → ℤ)
    (hf : ∀ i n, ModularFormClass.qCoeff (f i) n = (a i n : ℂ))
    (hli : LinearIndependent ℂ f) :
    Fintype.card ι ≤ Module.finrank F ↥(ModPForms.modPCusp N k F) := by sorry
