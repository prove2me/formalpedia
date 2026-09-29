-- Prove2me | Theorems.Thm_ModularCurve_JZero_naiveHeight_northcott
-- name    : ModularCurve.JZero.naiveHeight_northcott
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/f6509dfb-6dfa-574b-8152-c5e27b019d26
-- title:
--   Northcott property of the naive height on J₀(N)(K)
-- statement:
--   Fix a natural number $N \neq 0$ and an intermediate field $K$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$, i.e. a number field inside $\overline{\mathbb{Q}}$, together with a natural number $g'$. Work with the field $F =$ `modularFunctionFieldBar N`, the base change to $\overline{\mathbb{Q}}$ of the level-$N$ modular function field, realised as the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `modularFunctionFieldFull N`; its places are the valuation subrings of $F$ which contain $\overline{\mathbb{Q}}$, are not all of $F$ and are principal ideal rings, a divisor is a finitely supported $\mathbb{Z}$-valued function on places, $v.\mathrm{ord}$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation, and the degree of a divisor is the sum of its values weighted by the residue degrees of the places. The hypothesis $hR$ is a Riemann-type statement for this field: every divisor $D$ of degree at least $g'$ admits a nonzero $f \in F$ with $D v + v.\mathrm{ord}(f) \geq 0$ at every place $v$. Under these assumptions the function `JZero.naiveHeight N K g'` has the Northcott property: for every real bound, only finitely many elements of the fixed-point set $\mathrm{Pic}^0(F/\overline{\mathbb{Q}})^{K.\mathrm{fixingSubgroup}}$ have height at most that bound. Here the height of a class $c$ is the infimum of the numbers $\mathrm{divNaiveHeight}\,N\,K\,g'\,D$ taken over all effective divisors $D$ that are stable under the arithmetic Galois action of the subgroup of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing $K$ and are of the form $E + g' \cdot [\infty]$ with $E$ of degree zero representing $c$ in $\mathrm{Pic}^0$.
--
--   This is Northcott's finiteness theorem for the naive height on the Mordell–Weil group $J_0(N)(K)$, obtained from Northcott's theorem for projective space over a number field applied to the $j$-coordinates of a Galois-stable effective representative of degree $g'$. It supplies the finiteness input for the descent step [`ModularCurve.JZero.exists_descent_height_two_invariants_of_prime_of_five_le`](thm.html#ModularCurve.JZero.exists_descent_height_two_invariants_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_naiveHeight_northcott.lean

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.Order.Northcott

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.naiveHeight_northcott (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    (hR : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g' : ℤ) ≤ Divisor.degree D →
        ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
          ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f) :
    Northcott (JZero.naiveHeight N K g') := by sorry
