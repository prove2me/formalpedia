-- Prove2me | Theorems.Thm_ModularCurve_jZero_zsmul_surjective
-- name    : ModularCurve.jZero_zsmul_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/84cec8be-69e0-5af7-9740-e66fae475167
-- title:
--   Divisibility of J₀(N): multiplication by m≠0 is surjective
-- statement:
--   Let $N$ be a natural number, assumed nonzero, and let $m$ be a nonzero integer. Write $\bar F_N$ for `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$, realised as an intermediate field of the Laurent series field $\overline{\mathbb Q}((t))$ over $\overline{\mathbb Q}$, and let `JZero N` be $\operatorname{Pic}^0(\overline{\mathbb Q}, \bar F_N)$, that is, the quotient of the additive group of degree-zero divisors of $\bar F_N$ over $\overline{\mathbb Q}$ by its subgroup of principal divisors. The theorem asserts that the map $x \mapsto m \cdot x$ from `JZero N` to itself, for the integer scalar action on this quotient group, is surjective: every class in `JZero N` is $m$ times some class. Equivalently, the abelian group `JZero N` is divisible.
--
--   Classically this is the surjectivity of multiplication by $m \neq 0$ on the $\overline{\mathbb Q}$-points of the Jacobian $J_0(N)$, here in the divisor-class-group model of the Jacobian. It is used wherever a class has to be divided by an integer, for instance in the construction of elements of prescribed torsion and in the Hecke-compatibility and Eisenstein-quotient arguments for `JZero N`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jZero_zsmul_surjective.lean

import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.jZero_zsmul_surjective
    (N : ℕ) [NeZero N] (m : ℤ) (hm : m ≠ 0) :
    Function.Surjective (fun x : JZero N => m • x) := by sorry
