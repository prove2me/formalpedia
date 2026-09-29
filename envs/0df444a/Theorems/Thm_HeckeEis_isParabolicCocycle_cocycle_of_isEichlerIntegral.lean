-- Prove2me | Theorems.Thm_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral
-- name    : HeckeEis.isParabolicCocycle_cocycle_of_isEichlerIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/d7d80da1-bf33-5fbb-9d43-d741a354aaac
-- title:
--   Eichler integrals of cusp forms give parabolic cocycles
-- statement:
--   Fix natural numbers $N$ (nonzero) and $n$, and let $f$ be a cusp form of weight $(n:\mathbb{Z})+2$ for $\Gamma_0(N)$. Let $\rho$ denote the representation of $\Gamma_0(N)$ on the space [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25) of degree-$n$ homogeneous polynomials in $X_0,X_1$ over $\mathbb{C}$ obtained by restricting [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61) along the inclusion of $\Gamma_0(N)$ into $\mathrm{SL}_2(\mathbb{Z})$, where a matrix $M$ acts by the substitution $X_j \mapsto \sum_i M_{ij} X_i$. Let $F : \mathfrak{H} \to$ [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25) satisfy two hypotheses. First, $F$ is an Eichler integral of $f$: for every monomial exponent $d$ and every $\tau \in \mathfrak{H}$, the function $z \mapsto \mathrm{coeff}_d\bigl(F(\mathrm{ofComplex}\,z)\bigr)$ is differentiable at $\tau$ with derivative $f(\tau)\,\mathrm{coeff}_d\bigl((\tau X_0 + X_1)^n\bigr)$. Second, $F$ is an equivariant primitive for $\rho$: for each $\gamma \in \Gamma_0(N)$ the difference $F(\gamma \cdot \tau) - \rho(\gamma)F(\tau)$ is independent of $\tau$. The conclusion is that the associated cocycle $z(\gamma) = F(\gamma \cdot i) - \rho(\gamma)F(i)$ is parabolic in the sense that for every $\gamma \in \Gamma_0(N)$ with $(\mathrm{tr}\,\gamma)^2 = 4$ one has $z(\gamma) \in \mathrm{range}\bigl(\rho(\gamma) - 1\bigr)$.
--
--   This is the parabolicity (cuspidality) of the Eichler–Shimura cocycle attached to a cusp form of weight $n+2$, in the weight-$(n+2)$ coefficient module $\mathrm{Sym}^n$ of binary forms; it is what places the cocycle in parabolic cohomology rather than merely in $H^1$. It feeds the construction of the Eichler–Shimura map and the computation of its compatibility with the Hecke operators $T$ and $U$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.isParabolicCocycle_cocycle_of_isEichlerIntegral (N n : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F) :
    HeckeEis.IsParabolicCocycle
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle := by sorry
