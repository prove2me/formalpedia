-- Prove2me | Theorems.Thm_ModPForms_mem_modPMod_of_map_mem_modPMod
-- name    : ModPForms.mem_modPMod_of_map_mem_modPMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/09496fb7-88ee-5d47-a6bf-f60dfaf1b1d3
-- title:
--   Descent of the space modPMod along a field homomorphism
-- statement:
--   Fix a level $N \in \mathbb{N}$ and a weight $k \in \mathbb{Z}$, two fields $K$ and $L$, and a ring homomorphism $i : K \to L$. For a field $F$, [`ModPForms.modPMod N k F`](def/CuspForm_ModPForms.html#L12) denotes the $F$-submodule of $F[[q]]$ spanned by the set of those power series $\varphi$ for which there exist a modular form $f$ of weight $k$ on $\Gamma_0(N)$ and a sequence of integers $a : \mathbb{N} \to \mathbb{Z}$ such that the $n$-th coefficient of the $q$-expansion of $f$ (taken with width $1$, via [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19)) equals $a_n$ as a complex number for every $n$, and $\varphi$ is the power series whose $n$-th coefficient is the image of $a_n$ in $F$. The assertion is: if $\psi \in K[[q]]$ is a power series whose image `PowerSeries.map i ψ` under the coefficientwise application of $i$ lies in [`ModPForms.modPMod N k L`](def/CuspForm_ModPForms.html#L12), then $\psi$ itself lies in [`ModPForms.modPMod N k K`](def/CuspForm_ModPForms.html#L12). No hypothesis of primality, of positivity of $N$, or on the characteristic is imposed.
--
--   This is the base-change (descent) statement for the spaces of $q$-expansions spanned by reductions of integral weight-$k$ forms on $\Gamma_0(N)$: membership may be tested after any field extension, since the two spanning sets are the reductions of the same integer sequences. It is used in the construction of elements of these spaces from mod-$p$ form functions and in the proof that the relevant theta series does not lie in such a space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_mem_modPMod_of_map_mem_modPMod.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.mem_modPMod_of_map_mem_modPMod
    (N : ℕ) (k : ℤ) (K L : Type) [Field K] [Field L] (i : K →+* L)
    (ψ : PowerSeries K) (h : PowerSeries.map i ψ ∈ ModPForms.modPMod N k L) :
    ψ ∈ ModPForms.modPMod N k K := by sorry
