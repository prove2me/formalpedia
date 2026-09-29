-- Prove2me | Theorems.Thm_MegiddoLP_FixedDim_approachI_fraction
-- name    : MegiddoLP.FixedDim.approachI_fraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:10:37.180294+00:00
-- url     : https://prove2.me/theorems/6bb3d5a9-72a4-4f6b-8510-d2dccff34c1b
-- title:
--   Approach I: $2^{d-1}$ queries settle at least $\lfloor 2^{1-2^d}n\rfloor$ of $n$ hyperplanes in $\mathbb{R}^d$
-- statement:
--   Let $d\ge1$, and let $H_i=\{x\in\mathbb{R}^d: a_i^Tx=b_i\}$, $i=1,\dots,n$, be hyperplanes with $a_i\ne0$. Then there is a query strategy $T$ such that for every unknown point $x\in\mathbb{R}^d$:
--
--   1. $T$ makes at most $A(d)=2^{d-1}$ queries;
--   2. every position that $T$ reports is correct;
--   3. $T$ reports the position of $x$ for at least $\lfloor B(d)\,n\rfloor$ of the hyperplanes, where $B(d)=2^{1-2^d}$:
--
--   $$\#\{i:\ T\text{ reports the position of }x\text{ relative to }H_i\}\ \ge\ \Big\lfloor \frac{n}{2^{2^d-1}}\Big\rfloor.$$
--
--   The constants solve the paper's recursion $A(d)=2A(d-1)$, $B(d)=\tfrac12B(d-1)^2$ with $A(1)=1$, $B(1)=\tfrac12$. Repeating such a round and discarding the settled hyperplanes is what yields the $O(\log n)$ query bound and, in linear programming, the linear-time pruning.
--
--   **Formalization Note** The page's "at least $Bn$ hyperplanes" is read as $\lfloor Bn\rfloor$ (natural-number division). The page does not say how the non-integer count $Bn$ is rounded. The floor is exactly what the paper's pairing recursion yields: $\lfloor n/2\rfloor$ pairs, and $\lfloor\lfloor m/2^j\rfloor/2^j\rfloor=\lfloor m/2^{2j}\rfloor$. It coincides with the page whenever $2^{2^d-1}$ divides $n$.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §3.2, p. 118 (definition of A(d), B(d)) and p. 121 (Approach I, A(d) = 2^{d-1}, B(d) = 2^{1-2^d})

import Mathlib
import Definitions.Def_MegiddoLP_FixedDim_QueryTree

/-!
Megiddo, J. ACM 31 (1984), §3.2 pp. 118 and 121 (Approach I): `A(d) = 2^{d-1}` queries
suffice to determine the position of `x*` relative to at least `B(d)·n` of `n` given
hyperplanes in `ℝ^d`, where `B(d) = 2^{1-2^d}`. The count `B(d)·n` is read as
`⌊n / 2^{2^d - 1}⌋`.
-/

namespace MegiddoLP.FixedDim

/-- **Approach I: `A(d) = 2^{d-1}`, `B(d) = 2^{1-2^d}`.** For `d ≥ 1` and `n` hyperplanes
`{aᵢ ⬝ᵥ x = bᵢ}` in `ℝ^d` with `aᵢ ≠ 0`, there is a strategy which, for every unknown point `x`,
makes at most `2^{d-1}` queries and reports correct positions for at least
`⌊n / 2^{2^d - 1}⌋` of the hyperplanes. -/
theorem approachI_fraction (d n : ℕ) (hd : 1 ≤ d) (a : Fin n → Fin d → ℝ) (b : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    ∃ T : QTree d (Fin n → Option Ordering), ∀ x : Fin d → ℝ,
      T.numQueries x ≤ 2 ^ (d - 1) ∧
      (∀ i o, T.eval x i = some o → compare (a i ⬝ᵥ x) (b i) = o) ∧
      n / 2 ^ (2 ^ d - 1) ≤ (Finset.univ.filter fun i => (T.eval x i).isSome).card := by sorry

end MegiddoLP.FixedDim
