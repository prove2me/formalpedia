-- Prove2me | Theorems.Thm_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one
-- name    : HeckeCharacter.fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/5e3dad49-ab9f-51f3-bfef-831079655c50
-- title:
--   Content of a 1-adjusted idèle is coprime to f
-- statement:
--   Let $K$ be a number field and $\mathfrak f$ an ideal of $\mathcal O_K$, and let $u$ be a unit of the adèle ring of $K$ satisfying `IsAdjuster K 𝔣 u 1`, that is: (i) for every height-one prime $v$ of $\mathcal O_K$ with $v.\mathrm{asIdeal} \mid \mathfrak f$, the finite component at $v$ of $u \cdot (\iota(1))^{-1}$, where $\iota$ is induced by the structure map $K \to \mathbb A_K$, has valuation $1$ and its difference with $1$ has valuation at most $\exp(-n_v)$, where $n_v$ is the multiplicity of $v.\mathrm{asIdeal}$ in the factorisation of $\mathfrak f$; and (ii) for every real embedding $\tau : K \to \mathbb R$ the real projection of $u \cdot (\iota(1))^{-1}$ at $\tau$ is strictly positive. Then the fractional-ideal content of the finite part of $u$, namely the element $\prod_v^{\mathrm{f}} (\mathfrak p_v)^{\mathrm{placeOrd}}$ of the unit group of fractional ideals obtained by applying `fadContentHom K` to `projFin K u`, where the exponent at $v$ is $-\log$ of the valuation of the $v$-component, lies in the subgroup `coprimeToModulus K 𝔣`: its $v$-adic count vanishes for every height-one prime $v$ with $v.\mathrm{asIdeal} \mid \mathfrak f$.
--
--   This is the coprimality step in the idelic description of narrow ray class groups: it guarantees that the content of an idèle adjusted at level $\mathfrak f$ lies in the group of fractional ideals prime to $\mathfrak f$, so that the Artin symbol modulo $\mathfrak f$ may be evaluated on it. It is used in the comparison of the idelic Artin map with products of Frobenius symbols and in the construction of the isomorphism between idèle classes and the narrow ray class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter

theorem HeckeCharacter.fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : IsAdjuster K 𝔣 u 1) :
    fadContentHom K (projFin K u) ∈ coprimeToModulus K 𝔣 := by sorry
