-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_abelJacobiCard
-- name    : ModularCurve.JZero.exists_abelJacobiCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/903521f0-e7eb-5fd7-8f5a-934027838493
-- title:
--   p-power torsion of J₀(N) has order p^{2gn}
-- statement:
--   Let $N$ be a positive natural number. Write $F$ for the intermediate field of $\overline{\mathbb Q}((q))$ (Laurent series over an algebraic closure of $\mathbb Q$) generated over $\overline{\mathbb Q}$ by the image, under coefficientwise extension of scalars, of the field `modularFunctionFieldFull N`, itself the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the family `divisorExpansions N`; this is `modularFunctionFieldBar N`, the function field of $X_0(N)$ over $\overline{\mathbb Q}$. Let $\mathrm{Pic}^0$ denote the quotient of the group of degree-zero divisors of $F/\overline{\mathbb Q}$ by the subgroup of principal divisors. The theorem asserts: there exists a natural number $g$ such that for every prime $p$ and every natural number $n$, the $p^n$-torsion subgroup of $\mathrm{Pic}^0$, i.e. the elements killed by $p^n$, is finite of cardinality exactly $p^{2gn}$. The number $g$ is quantified existentially and is independent of $p$; no identification of $g$ with the genus of $X_0(N)$ is claimed.
--
--   This is the standard count $\#J_0(N)[p^n]=p^{2gn}$ for the $p$-power torsion of the Jacobian of $X_0(N)$ over an algebraically closed field of characteristic zero, in the divisor-class-group presentation used throughout the project. It is the input to the finiteness statement [`ModularCurve.jZeroTorsionFinite`](thm.html#ModularCurve.jZeroTorsionFinite) and to the computation of $\dim_{\mathbb F_p} J_0(N)[p]$, and hence feeds the Galois-representation and Mazur-principle arguments that use $p$-torsion of $J_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_abelJacobiCard.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_abelJacobiCard (N : ℕ) [NeZero N] : ∃ g : ℕ, ∀ (p : ℕ) [Fact p.Prime], AbelJacobiCard (AlgebraicClosure ℚ) (modularFunctionFieldBar N) p g := by sorry
