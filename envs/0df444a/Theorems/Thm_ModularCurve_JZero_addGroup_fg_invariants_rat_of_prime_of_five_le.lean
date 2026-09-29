-- Prove2me | Theorems.Thm_ModularCurve_JZero_addGroup_fg_invariants_rat_of_prime_of_five_le
-- name    : ModularCurve.JZero.addGroup_fg_invariants_rat_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/5747508a-bbc3-5c6f-b5fc-8646c49d0a47
-- title:
--   Finite generation of J₀(N)(ℚ) for prime N≥ 5
-- statement:
--   Let $N$ be a natural number which is nonzero (the `NeZero N` instance), prime (`hN`) and at least $5$ (`hN5`). The object `JZero N` is the group `Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`: places of the field `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ are valuation subrings containing the image of $\overline{\mathbb{Q}}$, different from the whole field and principal ideal rings; divisors are finitely supported $\mathbb{Z}$-valued functions on places; `Pic0` is the quotient of the subgroup of divisors of degree zero (degree being computed with the residue-field degrees `Place.deg`) by the subgroup of principal divisors $\operatorname{ord}(f)$. Here `modularFunctionFieldBar N` is `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)`, the subfield of `LaurentSeries (AlgebraicClosure ℚ)` generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of `modularFunctionFieldFull N`, which in turn is the subfield of `LaurentSeries ℚ` generated over $\mathbb{Q}$ by the series `qExpand ℚ d jq` for all nonzero divisors $d$ of $N$, with `jq` the explicit Laurent series $q^{-1}E_4(q)^3\prod_{n\ge 1}(1-q^n)^{-24}$. A $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ acts on Laurent series coefficientwise, preserves this field, and so acts semilinearly, hence on places, on degree-zero divisors and on `JZero N`; this is the action used. The conclusion is that the additive subgroup `FixedPoints.addSubgroup` of elements of `JZero N` fixed by every element of $\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}}$ is a finitely generated additive group. Nothing is asserted about its rank, its torsion, or the level $N$ beyond the hypotheses; the primality and the bound $5\le N$ are genuine hypotheses of this formal statement, although the classical theorem needs neither.
--
--   This is the Mordell–Weil theorem for the Jacobian of $X_0(N)$ over $\mathbb{Q}$: the group of rational points of $J_0(N)$ is finitely generated, in the shape used by arguments in the style of Mazur's work on the Eisenstein ideal. Relative to the textbook statement it is restricted to prime level $N\ge 5$, and the group of rational points is presented concretely as the subgroup of the divisor class group of the $\overline{\mathbb{Q}}$-model fixed by the whole group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$, rather than as points of a scheme over $\mathbb{Q}$. It feeds the finiteness and torsion statements about the Eisenstein quotient of the rational Hecke module, and the uniform bound on $h^0$ of the primary torsion sheaf attached to $J_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_addGroup_fg_invariants_rat_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.addGroup_fg_invariants_rat_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) :
    AddGroup.FG ↥(FixedPoints.addSubgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (JZero N)) := by sorry
