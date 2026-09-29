-- Prove2me | Theorems.Thm_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul
-- name    : ModularCurve.existsUnique_qExpand_sub_pow_eq_natCast_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/c807539c-3b44-5dd4-a643-28622b865338
-- title:
--   Kronecker congruence: f(q^q)-f(q)^q is uniquely q-divisible
-- statement:
--   Let $q$ be a prime and let $f$ be a Laurent series over $\mathbb Z$, i.e. an element of `LaurentSeries ℤ` (a Hahn series over $\mathbb Z$ with exponents in $\mathbb Z$ and well-founded support). Here `qExpand ℤ q` denotes the ring endomorphism of `LaurentSeries ℤ` obtained by pushing the exponent support forward along multiplication by $q$ on $\mathbb Z$ (an injective, order-preserving map since $q \neq 0$ and $q > 0$); concretely it is the substitution $\mathfrak q \mapsto \mathfrak q^{q}$, sending $\sum_n a_n \mathfrak q^{n}$ to $\sum_n a_n \mathfrak q^{qn}$. The assertion is that there exists a unique $S \in$ `LaurentSeries ℤ` such that $$\mathrm{qExpand}_{\mathbb Z,q}(f) - f^{q} = q \cdot S,$$ the factor $q$ being the image of the natural number $q$ under the canonical map $\mathbb N \to$ `LaurentSeries ℤ`. Thus the congruence $f(\mathfrak q^{q}) \equiv f(\mathfrak q)^{q} \pmod q$ holds, and the quotient by $q$ is well defined as a single Laurent series over $\mathbb Z$.
--
--   This is the Kronecker congruence in the formal variable: reduction modulo a prime $q$ turns substitution of $\mathfrak q^{q}$ into the $q$-th power map, and the uniqueness clause makes the divided difference $\bigl(f(\mathfrak q^{q})-f(\mathfrak q)^{q}\bigr)/q$ an honest integral Laurent series. It is used in the treatment of Frobenius lifts on modular curves, notably for the tube equation of level-one prolongation pairs and for the Kronecker-remainder differential equations of the Frobenius graph.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve

theorem ModularCurve.existsUnique_qExpand_sub_pow_eq_natCast_mul
    (q : ℕ) [Fact q.Prime] (f : LaurentSeries ℤ) :
    ∃! S : LaurentSeries ℤ, qExpand ℤ q f - f ^ q = (q : LaurentSeries ℤ) * S := by sorry
