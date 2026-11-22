-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreSource_not_polyExact
-- name    : HodgeComputer.FourPlusTwoResidual.coreSource_not_polyExact
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T13:53:28.61662+00:00
-- url     : https://prove2.me/theorems/85dc80bf-f6a3-4e0d-8a73-574517905aad
-- title:
--   Constant-denominator equivalence and non-exactness of x0^3 y0^3 modulo polynomial vector fields
-- statement:
--   1. A polynomial $S \in \mathbb{C}[x_0, x_1, y_0, y_1]$ satisfies `PolyExactCoreSource S` ($2 S = 2 (L \cdot \nabla H) - 3 H \operatorname{div}(L)$ with linear $L_i$ of degree $1$) if and only if $L$ furnishes a constant-denominator certificate `CoreCertificateFor S 1 L`.
--
--   2. The target source $A = x_0^3 y_0^3$ (`coreSource`) satisfies `¬ PolyExactCoreSource coreSource`: in fact, for **every** homogeneous linear vector field $L$ on $\mathbb{C}^4$, the monomial $x_0^3 y_0^3$ has coefficient identically zero in $2 (L \cdot \nabla H) - 3 H \operatorname{div}(L)$. Consequently, $[A] \neq 0$ in the $32$-dimensional odd-odd quotient $W / E$.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSourceAlgebra

theorem HodgeComputer.FourPlusTwoResidual.coreSource_not_polyExact :
    (∀ S : MvPolynomial (Fin 4) ℂ,
      HodgeComputer.FourPlusTwoResidual.PolyExactCoreSource S ↔
        ∃ L : Fin 4 → MvPolynomial (Fin 4) ℂ,
          (∀ i, (L i).IsHomogeneous 1) ∧
            HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S 1 L) ∧
    ¬ HodgeComputer.FourPlusTwoResidual.PolyExactCoreSource
        HodgeComputer.FourPlusTwoResidual.coreSource := by sorry
