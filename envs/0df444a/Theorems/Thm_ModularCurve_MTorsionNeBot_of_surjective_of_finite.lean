-- Prove2me | Theorems.Thm_ModularCurve_MTorsionNeBot_of_surjective_of_finite
-- name    : ModularCurve.MTorsionNeBot.of_surjective_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/135c090e-2a2d-5999-b6f7-d5d20563c8e8
-- title:
--   Nonzero 𝔪-torsion descends along surjections from finite modules
-- statement:
--   Let $\mathbb{T}$ be a commutative ring, let $\mathfrak{m}$ be an ideal of $\mathbb{T}$ (no maximality or finite generation of $\mathfrak{m}$ is assumed), and let $N$ and $N''$ be $\mathbb{T}$-modules, each an additive commutative group with a $\mathbb{T}$-module structure, with $N$ finite as a type. Let $f : N \to N''$ be a $\mathbb{T}$-linear map and suppose $f$ is surjective. The assertion is the implication $\mathrm{MTorsionNeBot}\,\mathbb{T}\,N''\,\mathfrak{m} \to \mathrm{MTorsionNeBot}\,\mathbb{T}\,N\,\mathfrak{m}$, where for a $\mathbb{T}$-module $J$ the predicate `MTorsionNeBot` says that the submodule of elements of $J$ annihilated by every element of $\mathfrak{m}$, namely `Submodule.torsionBySet 𝕋 J 𝔪`, is not the zero submodule. Thus: if $N''$ contains a nonzero element killed by all of $\mathfrak{m}$, then so does $N$. Note the direction — the hypothesis is on the quotient $N''$ and the conclusion on the finite source $N$.
--
--   This is the support-lifting step used when transferring nonvanishing of Hecke-eigenspace torsion from a quotient module to the module above it: in the language of supports, $\operatorname{Supp} N'' \subseteq \operatorname{Supp} N$, here expressed through non-vanishing of $\mathfrak{m}$-torsion. It is applied in the analysis of torsion in the Néron model of $J_0$ at $p$, by [`ModularCurve.JZeroNeronObjectAtP.hasLowerLevelTorsion_of_ptsSp_symm_fibreMap_abqFibre_ne_zero`](thm.html#ModularCurve.JZeroNeronObjectAtP.hasLowerLevelTorsion_of_ptsSp_symm_fibreMap_abqFibre_ne_zero) and [`ModularCurve.JZeroNeronObjectAtP.heckeTorsion_ne_bot_of_ptsSp_symm_fibreMap_abqFibre_ne_zero`](thm.html#ModularCurve.JZeroNeronObjectAtP.heckeTorsion_ne_bot_of_ptsSp_symm_fibreMap_abqFibre_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MTorsionNeBot_of_surjective_of_finite.lean

import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.MTorsionNeBot.of_surjective_of_finite {𝕋 : Type*} [CommRing 𝕋]
    {N N'' : Type*} [AddCommGroup N] [Module 𝕋 N] [AddCommGroup N''] [Module 𝕋 N''] (𝔪 : Ideal 𝕋)
    [Finite N] (f : N →ₗ[𝕋] N'') (hf : Function.Surjective f) :
    MTorsionNeBot 𝕋 N'' 𝔪 → MTorsionNeBot 𝕋 N 𝔪 := by sorry
