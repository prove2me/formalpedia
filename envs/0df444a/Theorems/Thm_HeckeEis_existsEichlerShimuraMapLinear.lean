-- Prove2me | Theorems.Thm_HeckeEis_existsEichlerShimuraMapLinear
-- name    : HeckeEis.existsEichlerShimuraMapLinear
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/0df9c703-9190-57ad-9fd3-324c5ce3ec81
-- title:
--   ℂ-linearity of the Eichler–Shimura map
-- statement:
--   Fix natural numbers $n$ and $N$ with $N \neq 0$. Let $\rho$ denote the representation of $\Gamma_0(N)$ obtained by restricting [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61) along the inclusion of $\Gamma_0(N)$ into $\mathrm{SL}(2,\mathbb{Z})$, that is, the action of $\mathrm{SL}(2,\mathbb{Z})$ on the space of degree-$n$ homogeneous polynomials in $\mathbb{C}[X_0,X_1]$ by the substitution $X_j \mapsto \sum_i M_{ij} X_i$ for $M$ the integral matrix underlying the group element. Let [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) $\rho$ be the quotient of the submodule of parabolic cocycles (those cocycles $z : \Gamma_0(N) \to \mathrm{BinaryForm}\,\mathbb{C}\,n$ with $z\gamma$ in the range of $\rho\gamma - 1$ whenever the trace of $\gamma$ has square $4$) by the submodule of coboundaries. The assertion is that there exists a $\mathbb{C}$-linear map $ES$ from the space of cusp forms of weight $(n : \mathbb{Z}) + 2$ for $\Gamma_0(N)$ to this parabolic cohomology module such that for every such cusp form $f$ one has $ES\,f =$ [`HeckeEis.eichlerShimuraMap`](def/HeckeEis_EichlerIntegral.html#L114) $n\,N$ applied to the underlying function $\mathbb{H} \to \mathbb{C}$ of $f$; the latter is, by definition, the class of the cocycle $\gamma \mapsto F(\gamma \cdot i) - \rho\gamma(F(i))$ of a chosen equivariant primitive $F$ that is an Eichler integral of $f$ with parabolic cocycle, when such an $F$ exists, and $0$ otherwise. The conclusion is a bare existential statement, so no particular linear map is named.
--
--   This is the linearity of the classical Eichler–Shimura map $S_{n+2}(\Gamma_0(N)) \to H^1_{\mathrm{par}}(\Gamma_0(N), \mathrm{Sym}^n)$, here realised with coefficients in binary forms of degree $n$ and with the class of a cusp form defined through a choice of admissible Eichler integral. It is used downstream in the injectivity of the Eichler–Shimura map and in the construction of integral and mod-$p$ eigenclasses in parabolic cohomology attached to Hecke eigenforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_existsEichlerShimuraMapLinear.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.existsEichlerShimuraMapLinear (n N : ℕ) [NeZero N] :
    ∃ ES : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2), ES f = HeckeEis.eichlerShimuraMap n N f := by sorry
