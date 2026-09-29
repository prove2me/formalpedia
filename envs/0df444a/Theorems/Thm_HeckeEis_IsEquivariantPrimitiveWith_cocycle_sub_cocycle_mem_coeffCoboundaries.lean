-- Prove2me | Theorems.Thm_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries
-- name    : HeckeEis.IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/64d2c2a5-369d-5e77-a6c0-6474236248c2
-- title:
--   Equivariant primitives differing by a constant: cohomologous cocycles
-- statement:
--   Let $K$ be a commutative ring, $\Gamma$ a subgroup of $\mathrm{SL}_2(\mathbb{Z})$, and $V$ a $K$-module carrying a representation $\rho$ of $\Gamma$. Let $F, G \colon \mathfrak{H} \to V$ be functions on the upper half-plane, each of which is an equivariant primitive for $\rho$ in the sense of [`HeckeEis.IsEquivariantPrimitiveWith`](def/HeckeEis_EichlerIntegral.html#L68): for every $\gamma \in \Gamma$ there exists $c \in V$ with $F(\gamma \tau) - \rho(\gamma) F(\tau) = c$ for all $\tau \in \mathfrak{H}$, and likewise for $G$. Assume further that there is $v \in V$ with $F(\tau) - G(\tau) = v$ for all $\tau$, i.e. $F$ and $G$ differ by the constant $v$. The associated cocycles are the functions $\Gamma \to V$ given by $\gamma \mapsto F(\gamma \cdot i) - \rho(\gamma) F(i)$ and $\gamma \mapsto G(\gamma \cdot i) - \rho(\gamma) G(i)$, evaluated at the point $i$ of $\mathfrak{H}$. The conclusion is that their difference lies in [`HeckeEis.coeffCoboundaries`](def/Gamma0CoeffCohomology.html#L45) $\rho$, the image of the $K$-linear map $V \to (\Gamma \to V)$ sending $w$ to $\gamma \mapsto \rho(\gamma) w - w$; concretely, the difference is the coboundary attached to $-v$. The proof uses the equivariance hypotheses only as the arguments needed to form the two cocycles, not their content.
--
--   This is the standard independence statement for the cocycle attached to an Eichler integral: changing the primitive by a constant changes its cocycle by a coboundary, so the class in coefficient cohomology is well defined. It is used in the identification of the Eichler–Shimura map with the class map into parabolic cohomology and in the Hecke-equivariance statements for that map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries
    {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K Γ V} {F G : UpperHalfPlane → V}
    (hF : HeckeEis.IsEquivariantPrimitiveWith ρ F) (hG : HeckeEis.IsEquivariantPrimitiveWith ρ G)
    {v : V} (h : ∀ τ : UpperHalfPlane, F τ - G τ = v) :
    hF.cocycle - hG.cocycle ∈ HeckeEis.coeffCoboundaries ρ := by sorry
