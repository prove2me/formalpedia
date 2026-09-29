-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorBar_cuspidalClass_self
-- name    : ModularCurve.heckeOperatorBar_cuspidalClass_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/9e482b3b-e65e-51d3-9827-e47062b9cf05
-- title:
--   Uₚ fixes the cuspidal class of J₀(p)
-- statement:
--   Let $p$ be a prime. Consider the degree-zero divisor class group `JZero p`, that is `Pic0` of the field `modularFunctionFieldBar p` over the coefficient field $\overline{\mathbb{Q}}$ = `AlgebraicClosure ℚ`, defined as the group of degree-zero divisors modulo the subgroup of principal divisors, and the Hecke endomorphism `heckeOperatorBar p` of this group, which at a prime $\ell$ is the $\mathbb{Z}$-linear map underlying `heckeOperatorAlong (AlgebraicClosure ℚ) p ℓ`; the latter is given by `heckePic0Bar` applied to the data packaged in `HeckeInputsAlong (AlgebraicClosure ℚ) p ℓ` when that predicate holds, and is the zero map otherwise. Let `cuspidalClass p` be the class in `JZero p` of the degree-zero divisor attached to `cuspidalDivisor p`, namely `Finsupp.single (cuspZeroBar p) 1 - Finsupp.single (cuspInftyBar p) 1`, the difference of the two cusps $0$ and $\infty$. The assertion is that `heckeOperatorBar p` evaluated at the prime $p$ itself fixes this class: the image of `cuspidalClass p` equals `cuspidalClass p`. In particular the eigenvalue is $1$, not $1+p$.
--
--   This is the $U_p$ case of the statement that the Hecke operators act on the cuspidal class of $J_0(p)$ by the Eisenstein eigenvalues, the operator at the level prime acting trivially rather than by $1+p$. It supplies the `hU` hypothesis of [`ModularCurve.eisensteinKernelKillsCuspidalClass_heckeModuleBar`](thm.html#ModularCurve.eisensteinKernelKillsCuspidalClass_heckeModuleBar) and thereby feeds [`ModularCurve.eisensteinIdeal_smul_cuspidalClass`](thm.html#ModularCurve.eisensteinIdeal_smul_cuspidalClass), the annihilation of the cuspidal class by the Eisenstein ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorBar_cuspidalClass_self.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.heckeOperatorBar_cuspidalClass_self (p : ℕ) [Fact p.Prime] : heckeOperatorBar p ⟨p, Fact.out⟩ (cuspidalClass p) = cuspidalClass p := by sorry
