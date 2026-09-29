-- Prove2me | Theorems.Thm_HeckeEis_eichlerShimuraMap_injective
-- name    : HeckeEis.eichlerShimuraMap_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/9c3ee924-f311-5337-9021-947198d5d895
-- title:
--   Injectivity of the Eichler–Shimura map on cusp forms
-- statement:
--   Let $N \ge 1$ and let $n \ge 0$ be natural numbers. Write $\rho$ for the representation of $\Gamma_0(N)$ obtained by restricting [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61), the substitution action of $\mathrm{SL}_2(\mathbb{Z})$ on the submodule `BinaryForm ℂ n` of degree-$n$ homogeneous polynomials in two variables over $\mathbb{C}$, along the inclusion of $\Gamma_0(N)$. The theorem asserts that the assignment sending a cusp form $f$ of weight $(n : \mathbb{Z}) + 2$ for $\Gamma_0(N)$ to [`HeckeEis.eichlerShimuraMap n N f`](def/HeckeEis_EichlerIntegral.html#L114) is an injective function. Here `eichlerShimuraMap n N f` is defined by cases: if there is some $F : \mathbb{H} \to$ `BinaryForm ℂ n` which is an Eichler integral of $f$ (for every multidegree $d$ and every $\tau$, the coefficient of $d$ in $F$, read as a function of the complex variable, has derivative $f(\tau)$ times the coefficient of $d$ in $(X_0 \tau + X_1)$-type form `linePow n τ` at $\tau$), which is an equivariant primitive for $\rho$ (for each $\gamma$ the difference $F(\gamma \cdot \tau) - \rho(\gamma)(F\tau)$ is independent of $\tau$) and whose associated cocycle $\gamma \mapsto F(\gamma \cdot i) - \rho(\gamma)(F i)$ is parabolic (for every $\gamma$ whose integral matrix has trace squared equal to $4$, its value lies in the image of $\rho(\gamma) - 1$), then the value is the class of that cocycle in `coeffH1par ρ`, the quotient of parabolic cocycles by coboundaries; otherwise the value is $0$. Thus two cusp forms of weight $n+2$ on $\Gamma_0(N)$ with the same parabolic cohomology class coincide.
--
--   This is the injectivity half of the Eichler–Shimura relation between weight-$(n+2)$ cusp forms on $\Gamma_0(N)$ and parabolic cohomology of $\Gamma_0(N)$ with coefficients in binary forms of degree $n$; it is the weight-$(n+2)$ analogue of injectivity of the period map on weight-$2$ forms. It is used in the construction of Hecke eigenclasses in `coeffH1par` attached to eigenforms and in the finiteness of the integral Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_eichlerShimuraMap_injective.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_injective (N : ℕ) [NeZero N] (n : ℕ) :
    Function.Injective
      (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦ HeckeEis.eichlerShimuraMap n N f) := by sorry
