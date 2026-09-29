-- Prove2me | Theorems.Thm_HeckeEis_coeffH1par_binaryFormRepSL_eq_zero_of_odd
-- name    : HeckeEis.coeffH1par_binaryFormRepSL_eq_zero_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/cbbf5965-74df-57a7-8920-8fa71b4b4cf4
-- title:
--   Vanishing of parabolic H¹ for odd symmetric powers
-- statement:
--   Let $K$ be a field in which $2 \neq 0$, let $N$ and $n$ be natural numbers with $n$ odd, and consider the representation of $\mathrm{SL}(2,\mathbb{Z})$ on the degree-$n$ binary forms [`HeckeEis.BinaryForm K n`](def/HeckeEis_BinaryFormRep.html#L25), that is on the submodule `MvPolynomial.homogeneousSubmodule (Fin 2) K n` of homogeneous polynomials of degree $n$ in two variables over $K$, where a matrix $M$ acts by the substitution $X_j \mapsto \sum_i M_{ij} X_i$ (the map [`HeckeEis.binaryFormRepSL K n`](def/HeckeEis_BinaryFormRep.html#L61)). Restrict this representation along the inclusion of the congruence subgroup $\Gamma_0(N)$ into $\mathrm{SL}(2,\mathbb{Z})$. The assertion is that every element $x$ of [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) of this restricted representation is zero; here `coeffH1par` of a representation $\rho$ of $\Gamma$ on $V$ is the quotient of the submodule of parabolic cocycles — those maps $\Gamma \to V$ lying in `coeffCocycles` and satisfying `IsParabolicCocycle` — by the preimage, under the inclusion of that submodule into all maps $\Gamma \to V$, of `coeffCoboundaries`, the range of `coeffCoboundaryMap`. Thus the parabolic first cohomology with coefficients in odd-degree binary forms vanishes, as a type-level statement about each of its elements.
--
--   This is the odd-weight companion of the Eichler–Shimura statements: since $-1 \in \Gamma_0(N)$ acts on binary forms of odd degree $n$ by $-1$, the parabolic cohomology group degenerates. It is used to dispose of the odd case in [`HeckeEis.isCompl_range_eichlerShimuraMap_range_conj`](thm.html#HeckeEis.isCompl_range_eichlerShimuraMap_range_conj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeffH1par_binaryFormRepSL_eq_zero_of_odd.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeffH1par_binaryFormRepSL_eq_zero_of_odd (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (N n : ℕ) (hn : Odd n)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)) : x = 0 := by sorry
