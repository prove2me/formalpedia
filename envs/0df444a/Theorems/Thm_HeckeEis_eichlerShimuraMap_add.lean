-- Prove2me | Theorems.Thm_HeckeEis_eichlerShimuraMap_add
-- name    : HeckeEis.eichlerShimuraMap_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/ead8ec67-bb2b-59c5-9770-0c35b45076fd
-- title:
--   Additivity of the Eichler–Shimura map on cusp forms
-- statement:
--   Fix natural numbers $n$ and $N$ with $N \neq 0$, and let $f, g$ be cusp forms of weight $(n : \mathbb{Z}) + 2$ for $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$. The map [`HeckeEis.eichlerShimuraMap n N`](def/HeckeEis_EichlerIntegral.html#L114) is defined on arbitrary functions $h : \mathbb{H} \to \mathbb{C}$ and takes values in [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) of the representation of $\Gamma_0(N)$ obtained by restricting [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61), the action of $\mathrm{SL}_2(\mathbb{Z})$ on the submodule $\mathrm{BinaryForm}\,\mathbb{C}\,n$ of degree-$n$ homogeneous polynomials in two variables by linear substitution; that target is the quotient of the module of parabolic coefficient cocycles by the coboundaries. By definition, the value at $h$ is the class of the cocycle $\gamma \mapsto F(\gamma \cdot i) - \rho(\gamma) F(i)$, for a choice of $F : \mathbb{H} \to \mathrm{BinaryForm}\,\mathbb{C}\,n$ that is an Eichler integral of $h$ (each coefficient of $F$, read as a function of a complex variable, has derivative the corresponding coefficient of $h(\tau) \cdot \mathrm{linePow}\,n\,\tau$ at every $\tau \in \mathbb{H}$), is an equivariant primitive (for each $\gamma$ the function $\tau \mapsto F(\gamma \cdot \tau) - \rho(\gamma)F(\tau)$ is constant), and whose cocycle is parabolic (its value at any $\gamma$ with $\mathrm{tr}(\gamma)^2 = 4$ lies in the range of $\rho(\gamma) - 1$); if no such $F$ exists the value is $0$. The assertion is that the value at the function underlying $f + g$ equals the sum of the values at the functions underlying $f$ and at $g$.
--
--   This is the additivity half of the linearity of the Eichler–Shimura map from weight-$(n+2)$ cusp forms on $\Gamma_0(N)$ to parabolic cohomology with coefficients in binary forms of degree $n$. Together with the corresponding homogeneity statement it feeds [`HeckeEis.existsEichlerShimuraMapLinear`](thm.html#HeckeEis.existsEichlerShimuraMapLinear), which packages the Eichler–Shimura map as a linear map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_eichlerShimuraMap_add.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.eichlerShimuraMap_add (n N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    HeckeEis.eichlerShimuraMap n N ⇑(f + g) = HeckeEis.eichlerShimuraMap n N f + HeckeEis.eichlerShimuraMap n N g := by sorry
