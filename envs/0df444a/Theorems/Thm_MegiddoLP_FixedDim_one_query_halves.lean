-- Prove2me | Theorems.Thm_MegiddoLP_FixedDim_one_query_halves
-- name    : MegiddoLP.FixedDim.one_query_halves
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:08:46.206984+00:00
-- url     : https://prove2.me/theorems/09690bc9-5ab5-4faf-a2b2-4f4629d1f9d0
-- title:
--   One query settles half of $n$ hyperplanes in $\mathbb{R}^1$: $A(1)=1$, $B(1)=\tfrac12$
-- statement:
--   Let $n\ge0$ and let $a_1,\dots,a_n$ be nonzero reals and $b_1,\dots,b_n$ reals, defining the "hyperplanes" $H_i=\{x\in\mathbb{R}: a_ix=b_i\}$ of the line. Then there is a query strategy $T$ (a hyperplane-query decision tree built from the data) such that for every unknown point $x\in\mathbb{R}$:
--
--   1. $T$ makes at most one query on $x$;
--   2. every position that $T$ reports for $x$ is correct: if $T$ reports "$<$", "$=$" or "$>$" for $H_i$, then $a_ix<b_i$, $a_ix=b_i$ or $a_ix>b_i$ respectively;
--   3. $T$ reports a position for at least half of the hyperplanes:
--
--   $$n\le 2\cdot\#\{i:\ T \text{ reports the position of } x \text{ relative to } H_i\}.$$
--
--   This is the one-dimensional base of Megiddo's multidimensional search. A query at the median of the points $b_i/a_i$ settles every point on the far side of the median. In the paper's notation, $A(1)=1$ query suffices for a fraction $B(1)=\tfrac12$ of the hyperplanes.
--
--   **Formalization Note** Points are `Fin 1 → ℝ`, and each $a_i$ is a nonzero vector in $\mathbb{R}^1$. The strategy's output assigns to each $i$ either nothing or a position (`Option Ordering`). "Half" is stated as $n\le2\cdot\#$settled, which for odd $n$ means at least $\lceil n/2\rceil$.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §3.1, p. 117 (median query) and §3.2, p. 118 (A(1) = 1, B(1) = 1/2)

import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_QueryTree

/-!
Megiddo, J. ACM 31 (1984), §3.1 p. 117 and §3.2 p. 118: in dimension one a single query
(at the median) settles the position of `x*` relative to at least half of `n` given
hyperplanes, i.e. `A(1) = 1`, `B(1) = 1/2`.
-/

namespace MegiddoLP.FixedDim

/-- **`A(1) = 1`, `B(1) = 1/2`.** For `n` hyperplanes `{x ∈ ℝ | aᵢ x = bᵢ}` with `aᵢ ≠ 0`
there is a strategy making at most one query which, for every unknown point `x`, reports
correct positions (`lt`/`eq`/`gt` of `aᵢ x` against `bᵢ`) for at least half of the hyperplanes
(`n ≤ 2 · #settled`). -/
theorem one_query_halves (n : ℕ) (a : Fin n → Fin 1 → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    ∃ T : QTree 1 (Fin n → Option Ordering), ∀ x : Fin 1 → ℝ,
      T.numQueries x ≤ 1 ∧
      (∀ i o, T.eval x i = some o → compare (a i ⬝ᵥ x) (b i) = o) ∧
      n ≤ 2 * (Finset.univ.filter fun i => (T.eval x i).isSome).card := by sorry

end MegiddoLP.FixedDim
