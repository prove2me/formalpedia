-- Prove2me | Theorems.Thm_MatousekLP_Simplex_bland_never_cycles
-- name    : MatousekLP.Simplex.bland_never_cycles
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T21:03:40.708974+00:00
-- url     : https://prove2.me/theorems/cb596417-2fe3-4c01-9652-d0f92966a9e2
-- title:
--   Theorem 5.8.1 — the simplex method with Bland's rule never cycles
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$ with $n\ge m$, $b\in\mathbb{R}^m$ and $c\in\mathbb{R}^n$, and consider the linear program "maximize $c^Tx$ subject to $Ax=b$, $x\ge0$". **Bland's rule** chooses as entering variable the variable with the smallest index among all nonbasic variables with a positive coefficient in the last row of the simplex tableau, and as leaving variable the one with the smallest index among all basic variables satisfying the ratio rule (5.3).
--
--   Then the simplex method with Bland's rule is always finite: there is no infinite sequence
--   $$B_0\to B_1\to B_2\to\cdots$$
--   in which every $B_{t+1}$ is obtained from the feasible basis $B_t$ by a pivot step following Bland's rule. Equivalently, since there are finitely many bases and each Bland step is determined by its starting basis, cycling is impossible.
--
--   Together with the optimality criterion and Lemma 5.6.1, the theorem shows that the simplex method, started from any feasible basis, ends after finitely many steps with an optimal basic feasible solution or a proof of unboundedness. The book notes that the duality theorem is an easy consequence.
--
--   **Formalization Note** Indices are 0-based, and "smallest index" compares variable indices. A Bland step is defined from the explicit tableau parameters of Lemma 5.5.1; it exists exactly when the tableau has some positive coefficient in the last row and some negative coefficient in the entering column, so the run stops precisely at an optimal or an unbounded tableau. The standing assumption of §4.2 ($n\ge m$, rank $A=m$) is a hypothesis.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 73, Theorem 5.8.1 (Bland's rule stated on p. 72)

import Mathlib
import Definitions.Def_MatousekLP_Simplex_Tableau
open Matrix Filter

namespace MatousekLP.Simplex

/-- Theorem 5.8.1 (p. 73). The simplex method with Bland's pivot rule is always finite: there is
no infinite sequence `B₀, B₁, B₂, …` of bases in which every `B_{t+1}` is obtained from the feasible
basis `B_t` by a pivot step with Bland's rule. Equivalently (there are finitely many bases and
the Bland step is deterministic), cycling is impossible.
Standing assumption of §4.2 (p. 44): `n ≥ m` and `A` has rank `m`. -/
theorem bland_never_cycles {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) :
    ¬ ∃ Bs : ℕ → Finset (Fin n), ∀ t, BlandStep A b c (Bs t) (Bs (t + 1)) := by sorry

end MatousekLP.Simplex
