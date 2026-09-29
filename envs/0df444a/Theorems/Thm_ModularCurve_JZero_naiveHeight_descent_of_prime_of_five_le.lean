-- Prove2me | Theorems.Thm_ModularCurve_JZero_naiveHeight_descent_of_prime_of_five_le
-- name    : ModularCurve.JZero.naiveHeight_descent_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/88fbf992-85f9-5a86-8362-64f174bdf26e
-- title:
--   Descent inequalities for the naive height on J₀(N)
-- statement:
--   Let $N$ be a nonzero natural number which is prime and at least $5$, let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ which is finite-dimensional over $\mathbb{Q}$, and let $g'$ be a natural number. Assume the Riemann-type hypothesis $hR$: for every divisor $D$ on the function field `modularFunctionFieldBar N` (the base change to $\overline{\mathbb{Q}}$ of the modular function field of level $N$, a divisor being a finitely supported $\mathbb{Z}$-valued function on its places) whose degree $\sum_v D(v)\deg v$ is at least $g'$, there is a nonzero $f$ in that field with $0 \le D(v) + \operatorname{ord}_v f$ at every place $v$, i.e. $D + \operatorname{div} f$ is effective. Write $h$ for `JZero.naiveHeight N K g'`, the function on the subgroup of elements of $\mathrm{Pic}^0$ of `modularFunctionFieldBar N` fixed by the image of the fixing subgroup of $K$, defined as the infimum of the naive heights $\mathrm{divNaiveHeight}$ of the effective, fixing-subgroup-invariant divisors of the form $E + g'\cdot(\infty)$ with $E$ of degree zero representing the given class. The conclusion asserts the existence of $k \in \mathbb{N}$, reals $a, b, c_0$ and a function $c$ on that group with $0 \le a < b$ such that $h(x) \le a\,h(g+x) + c(g)$ for all $g$ and $x$, and $b\,h(x) - c_0 \le h(2^k x)$ for all $x$.
--
--   These are the two inequalities required, alongside the Northcott property and finiteness of the quotient by $2^k$, by the abstract descent argument proving the Mordell–Weil theorem for the Jacobian $J_0(N)$ over a number field; the statement is cited by [`ModularCurve.JZero.exists_descent_height_two_invariants_of_prime_of_five_le`](thm.html#ModularCurve.JZero.exists_descent_height_two_invariants_of_prime_of_five_le). Classically both inequalities come from comparing the naive height with the canonical height, which would yield them with any $a > 1$ and $b$ slightly below $4^k$; here only the qualitative shape $0 \le a < b$ is asserted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_naiveHeight_descent_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Mathlib.Algebra.Ring.Action.Submonoid
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.naiveHeight_descent_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    (hR : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g' : ℤ) ≤ Divisor.degree D →
        ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
          ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f) :
    ∃ (k : ℕ) (a b c₀ : ℝ) (c : ↥(JZero N ^+ ↥K.fixingSubgroup) → ℝ), 0 ≤ a ∧ a < b ∧
      (∀ g x, JZero.naiveHeight N K g' x ≤ a * JZero.naiveHeight N K g' (g + x) + c g) ∧
      (∀ x, b * JZero.naiveHeight N K g' x - c₀ ≤ JZero.naiveHeight N K g' (2 ^ k • x)) := by sorry
