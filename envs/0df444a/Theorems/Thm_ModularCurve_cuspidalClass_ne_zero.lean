-- Prove2me | Theorems.Thm_ModularCurve_cuspidalClass_ne_zero
-- name    : ModularCurve.cuspidalClass_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/b1345e7e-f449-5b3d-bb97-2925d81badbe
-- title:
--   Nonvanishing of the cuspidal class at prime level
-- statement:
--   Let $p$ be a prime number which is not one of $2,3,5,7,13$ (the hypothesis is membership failure in the finite set $\{2,3,5,7,13\}$ of naturals). The assertion is that `cuspidalClass p` is nonzero in `JZero p`. Here `modularFunctionFieldBar p` is the modular function field of level $p$ over the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$, and `JZero p` is `Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar p)`, the quotient of the group of degree-zero divisors of that function field by the subgroup of principal divisors lying in degree zero. The class `cuspidalClass p` is the image under `Pic0.mk` of `cuspidalDivisor₀ p`, the degree-zero packaging of the divisor `cuspidalDivisor p` $=$ `Finsupp.single (cuspZeroBar p) 1 - Finsupp.single (cuspInftyBar p) 1`, i.e. the difference of the two distinguished cuspidal places $\bar 0$ and $\bar\infty$. Thus the conclusion states exactly that the divisor $(\bar 0) - (\bar\infty)$ is not principal in `modularFunctionFieldBar p`.
--
--   This is the nonvanishing of the cuspidal class of $J_0(p)$, classically the statement that $(\bar 0)-(\bar\infty)$ has order $\mathrm{num}((p-1)/12) > 1$ outside the genus-zero levels $p \in \{2,3,5,7,13\}$ (Ogg; Mazur). It feeds [`ModularCurve.cuspidalClassSurvives_heckeModuleBar`](thm.html#ModularCurve.cuspidalClassSurvives_heckeModuleBar), and through it the inputs of Mazur's argument on rational points of $X_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_cuspidalClass_ne_zero.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.cuspidalClass_ne_zero (p : ℕ) [Fact p.Prime]
    (hp : p ∉ ({2, 3, 5, 7, 13} : Finset ℕ)) :
    cuspidalClass p ≠ 0 := by sorry
