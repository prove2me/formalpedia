-- Prove2me | Theorems.Thm_HeckeEis_eichlerShimuraMap_smul
-- name    : HeckeEis.eichlerShimuraMap_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/92c28018-0953-5786-b828-29d55715c40d
-- title:
--   Complex homogeneity of the Eichler–Shimura map
-- statement:
--   Fix natural numbers $n$ and $N$ with $N \neq 0$, a scalar $c \in \mathbb{C}$, and a cusp form $f$ of weight $(n : \mathbb{Z}) + 2$ for $\Gamma_0(N)$. Write $\rho$ for the representation of $\Gamma_0(N)$ on the space `BinaryForm ℂ n` of homogeneous polynomials of degree $n$ in two variables over $\mathbb{C}$ obtained by restricting, along the inclusion of $\Gamma_0(N)$ into $\mathrm{SL}_2(\mathbb{Z})$, the substitution action `binaryFormRepSL ℂ n`. For a function $g : \mathbb{H} \to \mathbb{C}$, [`HeckeEis.eichlerShimuraMap n N g`](def/HeckeEis_EichlerIntegral.html#L114) is defined by cases: if there is an $F : \mathbb{H} \to$ `BinaryForm ℂ n` which is an Eichler integral of $g$ (each polynomial coefficient of $F$, read as a function of the complex variable, has derivative $g(\tau)$ times the corresponding coefficient of `linePow n τ` at every point of $\mathbb{H}$), which satisfies `IsEquivariantPrimitiveWith`, i.e. $F(\gamma \cdot \tau) - \rho(\gamma)F(\tau)$ is independent of $\tau$ for each $\gamma \in \Gamma_0(N)$, and whose associated cocycle $\gamma \mapsto F(\gamma \cdot i) - \rho(\gamma)F(i)$ is parabolic (for every $\gamma$ whose integral matrix has trace squared equal to $4$, its value lies in the image of $\rho(\gamma) - 1$), then the value is the class of that cocycle in `coeffH1par ρ`, the quotient of the parabolic cocycles by the coboundaries; otherwise the value is $0$. The assertion is that the value of this map on the function underlying $c \bullet f$ equals $c$ times its value on the function underlying $f$, for the $\mathbb{C}$-module structure on `coeffH1par ρ`.
--
--   This records the homogeneity half of the $\mathbb{C}$-linearity of the Eichler–Shimura map from weight $n+2$ cusp forms on $\Gamma_0(N)$ to parabolic cohomology with coefficients in the $n$-th symmetric power. It is used, together with the corresponding additivity statement, to package the Eichler–Shimura construction as a linear map in [`HeckeEis.existsEichlerShimuraMapLinear`](thm.html#HeckeEis.existsEichlerShimuraMapLinear).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_eichlerShimuraMap_smul.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_smul (n N : ℕ) [NeZero N] (c : ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    HeckeEis.eichlerShimuraMap n N ⇑(c • f) = c • HeckeEis.eichlerShimuraMap n N f := by sorry
