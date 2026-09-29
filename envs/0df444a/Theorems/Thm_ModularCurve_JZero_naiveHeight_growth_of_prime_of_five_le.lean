-- Prove2me | Theorems.Thm_ModularCurve_JZero_naiveHeight_growth_of_prime_of_five_le
-- name    : ModularCurve.JZero.naiveHeight_growth_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/c1c24573-1e1d-5ed1-b482-a0c601b9c309
-- title:
--   Height growth under 2^k on J₀(N), prime level ≥ 5
-- statement:
--   Fix a natural number $N \neq 0$ that is prime with $5 \le N$, an intermediate field $K$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$, and a natural number $g'$. The hypothesis `hR` asks that every divisor $D$ on the function field `modularFunctionFieldBar N` (the base change to $\overline{\mathbb{Q}}$ of the level-$N$ modular function field, viewed inside Laurent series over $\overline{\mathbb{Q}}$) with $g' \le \deg D$, the degree being $\sum_v D(v)\,\deg v$ over the finitely many places in its support, admits a nonzero element $f$ of that field with $0 \le D(v) + \mathrm{ord}_v(f)$ at every place $v$; that is, $D$ is linearly equivalent to an effective divisor. Let $A$ be a real number. Then there are $k \in \mathbb{N}$ and $C \in \mathbb{R}$ such that for every element $x$ of the fixed subgroup of `JZero N` $= \mathrm{Pic}^0$ of that function field under the fixing subgroup of $K$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, one has $A \cdot h(x) - C \le h(2^k \cdot x)$. Here $h =$ `JZero.naiveHeight N K g'` is the infimum of the values `divNaiveHeight N K g' D` over divisors $D$ that are effective, of the shape $E + g' \cdot (\text{cusp at } \infty)$ with $E$ of degree zero representing $x$, and invariant under the arithmetic Galois action of the fixing subgroup of $K$.
--
--   This is the growth (duplication) inequality for the naive height used in the Mordell–Weil descent for the Jacobian of $X_0(N)$: the order of quantifiers matters, since $k$ is allowed to depend on the prescribed factor $A$, a single doubling not being guaranteed to amplify this particular height. It feeds the descent statement [`ModularCurve.JZero.naiveHeight_descent_of_prime_of_five_le`](thm.html#ModularCurve.JZero.naiveHeight_descent_of_prime_of_five_le), and its proof cites the upper and lower comparisons between `divNaiveHeight` and the quadratic height form together with the quasi-invariance of that form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_naiveHeight_growth_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Mathlib.Algebra.Ring.Action.Submonoid
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.naiveHeight_growth_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    (hR : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g' : ℤ) ≤ Divisor.degree D →
        ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
          ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f)
    (A : ℝ) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : ↥(JZero N ^+ ↥K.fixingSubgroup),
      A * JZero.naiveHeight N K g' x - C ≤ JZero.naiveHeight N K g' (2 ^ k • x) := by sorry
