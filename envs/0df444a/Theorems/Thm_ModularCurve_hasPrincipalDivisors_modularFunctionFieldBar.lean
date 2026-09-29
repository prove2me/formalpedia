-- Prove2me | Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar
-- name    : ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/203f466e-501a-57ea-b9c6-211b1bfca7d2
-- title:
--   Principal divisors on the function field of X₀(N) over ℚ̄
-- statement:
--   Fix a natural number $N$ with $N \neq 0$, and assume `ModularPolynomialFamily`: for every prime $\ell$ (nonzero) there is a datum consisting of a polynomial $\Phi \in \mathbb{Z}[X][Y]$ that is monic, has degree equal to `dedekindPsi` $\ell$, satisfies $\Phi(j, j_\ell) = 0$ when evaluated by `evalAtJ` on the coefficients and at the Laurent series `jqN` $\ell$, and is symmetric in the sense that for all Laurent series $x, y$ over $\mathbb{Q}$ the two evaluations of $\Phi$ obtained by substituting $x$ into the coefficients and $y$ into the outer variable, and vice versa, agree. The conclusion is `HasPrincipalDivisors` for the field extension $\overline{\mathbb{Q}} \subseteq$ `modularFunctionFieldBar` $N$, the latter being the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `modularFunctionFieldFull` $N$, itself the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `divisorExpansions` $N$. Concretely: for every nonzero $f$ in that field there is a finitely supported integer-valued function $D$ on the places of the extension (valuation subrings of the Laurent series field containing $\overline{\mathbb{Q}}$, proper, and principal ideal rings) with $D(v) = \operatorname{ord}_v(f)$ for every place $v$, and with $\sum_v D(v) \deg(v) = 0$.
--
--   This is the statement that the divisor of a nonzero function on $X_0(N)$ over $\overline{\mathbb{Q}}$ is a well-defined finitely supported divisor of degree zero — the classical degree-zero theorem for principal divisors in an algebraic function field, here for the $q$-expansion model $\overline{\mathbb{Q}}(j(q^d) : d \mid N)$ whose degree-zero divisor class group plays the role of $J_0(N)(\overline{\mathbb{Q}})$. It supplies the `HasPrincipalDivisors` instance assumed by the statements about places, specialisations and Hecke correspondences on this function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by sorry
