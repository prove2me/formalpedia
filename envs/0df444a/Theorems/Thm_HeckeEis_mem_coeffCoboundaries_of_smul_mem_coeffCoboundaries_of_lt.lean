-- Prove2me | Theorems.Thm_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt
-- name    : HeckeEis.mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/0059caee-8085-5cf0-a114-d3dfb5252481
-- title:
--   No π-torsion in H¹(Γ₀(N), Symⁿ) when n<p
-- statement:
--   Let $R$ be a commutative ring, $K$ a field, and $p$ a prime with $K$ of characteristic $p$; let $\varphi : R \to K$ be a surjective ring homomorphism and $\pi \in R$ an element whose multiples are exactly the elements killed by $\varphi$, i.e. $\varphi(r) = 0 \iff \pi \mid r$, and such that multiplication by $\pi$ on $R$ is injective. Let $n, N$ be natural numbers with $n < p$ and $p \nmid N$. Consider the representation of $\Gamma_0(N) \le \mathrm{SL}(2,\mathbb{Z})$ on $\mathrm{BinaryForm}\ R\ n$, the $R$-submodule of degree-$n$ homogeneous polynomials in $R[X_0,X_1]$, obtained by restricting along the inclusion of $\Gamma_0(N)$ the action of $g \in \mathrm{SL}(2,\mathbb{Z})$ on $\mathrm{SL}(2,\mathbb{Z})$ by the substitution $X_j \mapsto \sum_i g_{ij} X_i$. Let $z : \Gamma_0(N) \to \mathrm{BinaryForm}\ R\ n$ be an inhomogeneous $1$-cocycle, i.e. $z(gh) = z(g) + g \cdot z(h)$ for all $g,h$. Assume $\pi z$ is a coboundary, that is, $\pi z(g) = g \cdot v - v$ for all $g$ for some degree-$n$ form $v$. The conclusion is that $z$ itself is a coboundary: $z(g) = g \cdot w - w$ for all $g \in \Gamma_0(N)$ for some degree-$n$ form $w$.
--
--   This is the statement that the first cohomology of $\Gamma_0(N)$ with coefficients in the binary forms of degree $n < p$ over $R$ has no $\pi$-torsion, in the concrete form of cocycles and coboundaries; the vanishing input is that a degree-$n$ form over $K$ fixed by all of $\Gamma_0(N)$ vanishes when $0 < n < p$ and $p \nmid N$. It is used in the construction of mod $p$ eigenforms attached to an eigensystem on $H^1(\Gamma_0(N), \mathrm{Sym}^3)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.mem_coeffCoboundaries_of_smul_mem_coeffCoboundaries_of_lt
    {R K : Type} [CommRing R] [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (φ : R →+* K) (hφ : Function.Surjective φ) (π : R) (hker : ∀ r : R, φ r = 0 ↔ π ∣ r)
    (hπ : IsSMulRegular R π) (n N : ℕ) (hnp : n < p) (hpN : ¬ p ∣ N)
    (z : ↥(HeckeEis.coeffCocycles
      ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)))
    (hz : π • (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) ∈
      HeckeEis.coeffCoboundaries
        ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)) :
    (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) ∈
      HeckeEis.coeffCoboundaries
        ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) := by sorry
