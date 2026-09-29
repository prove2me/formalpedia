-- Prove2me | Theorems.Thm_HeckeEis_mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero
-- name    : HeckeEis.mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/0a9ae621-239f-5659-8048-ca0f8a7474a8
-- title:
--   Vanishing cusp values force parabolicity of Γ₀(N)-cocycles
-- statement:
--   Let $K$ be a field of characteristic zero, let $N \geq 1$, and let $n$ be an even natural number. Write $V_n =$ [`HeckeEis.BinaryForm K n`](def/HeckeEis_BinaryFormRep.html#L25) for the submodule of homogeneous polynomials of degree $n$ in $K[X_0, X_1]$, and let $\rho$ denote the representation [`HeckeEis.binaryFormRepSL K n`](def/HeckeEis_BinaryFormRep.html#L61) of $\mathrm{SL}(2,\mathbb{Z})$ on $V_n$, under which $g$ acts by the substitution $X_j \mapsto \sum_i \bar{g}_{ij} X_i$ (entries of $g$ taken in $K$); the relevant representation of $\Gamma_0(N)$ is the restriction of $\rho$ along the inclusion of $\Gamma_0(N)$ into $\mathrm{SL}(2,\mathbb{Z})$. Let $z \colon \Gamma_0(N) \to V_n$ be a function satisfying the inhomogeneous cocycle identity $z(gh) = z(g) + \rho(g)\,z(h)$ for all $g, h \in \Gamma_0(N)$. Assume that for every $\sigma \in \mathrm{SL}(2,\mathbb{Z})$ and every $\gamma \in \Gamma_0(N)$ whose image in $\mathrm{SL}(2,\mathbb{Z})$ equals $\sigma T^N \sigma^{-1}$, where $T =$ `ModularGroup.T`, the coefficient of the monomial $X_1^n$ in $\rho(\sigma^{-1})\,z(\gamma)$ is zero. Then $z$ is a parabolic cocycle: it satisfies the cocycle identity and, for every $\gamma \in \Gamma_0(N)$ whose associated integer matrix has trace with square equal to $4$, one has $z(\gamma) \in \mathrm{range}\bigl(\rho(\gamma) - 1\bigr)$.
--
--   This is the criterion that a class in $H^1(\Gamma_0(N), V_n)$ all of whose boundary values at the cusps vanish is already parabolic, the quantity $\operatorname{coeff}_{X_1^n}(\rho(\sigma)^{-1} z(\sigma T^N \sigma^{-1}))$ being the boundary value at the cusp $\sigma\infty$. It is used in the construction of the Eichler–Shimura comparison, where a given cocycle is corrected by an Eisenstein contribution so as to land in the parabolic subspace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero
    {K : Type*} [Field K] [CharZero K] (N : ℕ) [NeZero N] (n : ℕ) (hn : Even n)
    {z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)}
    (hz : z ∈ HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (h : ∀ (σ : SL(2, ℤ)) (γ : CongruenceSubgroup.Gamma0 N),
      (γ : SL(2, ℤ)) = σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ →
        MvPolynomial.coeff (Finsupp.single 1 n)
          ((HeckeEis.binaryFormRepSL K n σ⁻¹ (z γ) : ↥(HeckeEis.BinaryForm K n)) : MvPolynomial (Fin 2) K) = 0) :
    z ∈ HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) := by sorry
