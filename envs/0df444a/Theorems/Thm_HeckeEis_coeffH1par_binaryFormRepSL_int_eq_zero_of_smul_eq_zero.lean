-- Prove2me | Theorems.Thm_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero
-- name    : HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/b8ca5bd8-e4bd-507a-b928-7ea9d7e6c033
-- title:
--   Torsion-freeness of integral parabolic H¹ for Γ₀(N)
-- statement:
--   Fix natural numbers $n$ and $N$ with $N \neq 0$. Let $V =$ [`HeckeEis.BinaryForm ℤ n`](def/HeckeEis_BinaryFormRep.html#L25) be the $\mathbb{Z}$-submodule of homogeneous polynomials of degree $n$ in $\mathbb{Z}[X_0, X_1]$, and let $\rho$ be the representation of $\Gamma_0(N)$ on $V$ obtained by composing the inclusion $\Gamma_0(N) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ with [`HeckeEis.binaryFormRepSL ℤ n`](def/HeckeEis_BinaryFormRep.html#L61), the action in which $g$ acts by the substitution sending $X_j$ to $\sum_i g_{ij} X_i$. The module [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) of this representation is the quotient of the submodule [`HeckeEis.coeffParabolicCocycles`](def/Gamma0CoeffCohomology.html#L75) of functions $z : \Gamma_0(N) \to V$ that lie in [`HeckeEis.coeffCocycles`](def/Gamma0CoeffCohomology.html#L13) and satisfy the predicate [`HeckeEis.IsParabolicCocycle`](def/Gamma0CoeffCohomology.html#L71), by the preimage, under the inclusion of that submodule into $\Gamma_0(N) \to V$, of [`HeckeEis.coeffCoboundaries`](def/Gamma0CoeffCohomology.html#L45), the range of the map [`HeckeEis.coeffCoboundaryMap`](def/Gamma0CoeffCohomology.html#L30). The assertion is that this quotient has no nonzero torsion: for every integer $m \neq 0$ and every class $x$ in it with $m \cdot x = 0$, one has $x = 0$.
--
--   This is the torsion-freeness of the integral parabolic cohomology group $H^1_{\mathrm{par}}(\Gamma_0(N), \mathrm{Sym}^n)$ in its inhomogeneous-cocycle description. It underlies the comparison of these groups across coefficient rings: it is used for the injectivity of the change-of-coefficients map from $\mathbb{Z}$ to $\mathbb{Q}$, for the construction of a basis of the complex parabolic cohomology compatible with the integral one, and for the divisibility statement [`HeckeEis.exists_eq_prime_smul_of_coeffH1par_map_eq_zero`](thm.html#HeckeEis.exists_eq_prime_smul_of_coeffH1par_map_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero (n N : ℕ) [NeZero N] (m : ℤ) (hm : m ≠ 0)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hx : m • x = 0) : x = 0 := by sorry
