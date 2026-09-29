-- Prove2me | Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
-- name    : ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/d2abfd39-e2b8-55b8-941b-8ca1018f502b
-- title:
--   Principal divisors on the ℚ̄-function field of X_H(M)
-- statement:
--   Let $M$ be a natural number with $M \neq 0$ and let $H$ be a subgroup of $(\mathbb Z/M\mathbb Z)^{\times}$. Write $F$ for the intermediate field `xHFunctionFieldBar M H` of the Laurent series field $\overline{\mathbb Q}((q))$ over $\overline{\mathbb Q}$, namely `laurentBaseChange` applied to the rational $q$-expansion field `xHFunctionField M H` $=$ `xHFunctionFieldC ℚ M H`: the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the image of `xHFunctionField M H` $\subset \mathbb Q((q))$ under the coefficientwise embedding $\mathbb Q((q)) \to \overline{\mathbb Q}((q))$. The assertion is the class `HasPrincipalDivisors` for $F$ over $\overline{\mathbb Q}$: for every $f \in F$ with $f \neq 0$ there exists a finitely supported function $D$ from the places of $F$ over $\overline{\mathbb Q}$ to $\mathbb Z$ — a place being a valuation subring of $F$ that contains the image of $\overline{\mathbb Q}$, is not all of $F$, and is a principal ideal ring — such that $D(v) = \operatorname{ord}_v(f)$ for every place $v$, and such that the degree $\sum_v D(v)\cdot \deg v$ of $D$ vanishes. Thus $f$ has only finitely many zeros and poles, counted with multiplicity and residue degree, and their total degree is zero.
--
--   This is the classical statement that on the modular curve $X_H(M)$ over $\overline{\mathbb Q}$, realised through its field of $q$-expansions, every non-zero function has a divisor which is finitely supported and of degree zero. It is the form in which the divisor theory of $X_H(M)$ is consumed downstream, for instance in the torus-coordinate descriptions of the Néron model of $J_H(M)$ at a prime $p$ and in the pole-order estimates for functions on $X_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := by sorry
