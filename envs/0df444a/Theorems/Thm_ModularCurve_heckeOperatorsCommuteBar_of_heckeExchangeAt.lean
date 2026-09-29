-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt
-- name    : ModularCurve.heckeOperatorsCommuteBar_of_heckeExchangeAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/b83cccc3-a7da-599a-903e-69457cb05cee
-- title:
--   Commutativity of Hecke operators from the exchange identity
-- statement:
--   Let $N \ge 1$ be a natural number. Two hypotheses are assumed, both stated over the base field $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. First, `hP`: for every $M \ge 1$ the field `modularFunctionFieldBar M`, i.e. the $\overline{\mathbb{Q}}$-subfield of $\overline{\mathbb{Q}}((q))$ obtained by base change (`laurentBaseChange`) of `modularFunctionFieldFull M`, satisfies `HasPrincipalDivisors`: every nonzero $f$ in it admits a divisor $D$ (a finitely supported $\mathbb{Z}$-valued function on the places of the field over $\overline{\mathbb{Q}}$) with $D(v) = v.\mathrm{ord}(f)$ at every place $v$ and $\deg D = 0$. Second, `hex`: for all primes $\ell \ne \ell'$ and every $M \ge 1$ with $M = N\ell\ell'$, the predicate `HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ ℓ' M hM` holds; that is, granted principal divisors at levels $N\ell$ and $M$ and integrality of the four maps involved, for every divisor $D$ on level $N\ell'$ the pullback along `heckeBetaBar` of the pushforward along `heckeAlphaBar` of $D$ equals the pushforward along `towerInclBar` of the pullback along `towerSubstBar` of $D$. The conclusion is `HeckeOperatorsCommuteBar N`: for all primes $\ell, \ell'$ the endomorphisms `heckeOperatorBar N ℓ` and `heckeOperatorBar N ℓ'` of the $\mathbb{Z}$-module `JZero N` commute.
--
--   This is the commutativity of the Hecke operators $T_\ell$ on $J_0(N)$, reduced here to two geometric inputs: existence of principal divisors of degree zero at every level, and the exchange identity between the two degeneracy legs at the roof level $N\ell\ell'$. It is the form in which commutativity enters the Hecke-module structure used later, and it is invoked by [`ModularCurve.heckeOperatorsCommuteBar`](thm.html#ModularCurve.heckeOperatorsCommuteBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean

import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.heckeOperatorsCommuteBar_of_heckeExchangeAt (N : ℕ) [NeZero N] (hP : ∀ (M : ℕ) [NeZero M], HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) (hex : ∀ (ℓ ℓ' M : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M] (hM : M = N * ℓ * ℓ'), ℓ ≠ ℓ' → HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ ℓ' M hM) : HeckeOperatorsCommuteBar N := by sorry
