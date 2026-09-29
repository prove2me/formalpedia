-- Prove2me | Theorems.Thm_LinearOptimization_lp_active_constraint_equiv
-- name    : LinearOptimization.lp_active_constraint_equiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T13:54:04.816173+00:00
-- url     : https://prove2.me/theorems/035b04e5-ef48-4d7a-9b6f-3a7d2181aa70
-- title:
--   Equivalent characterizations of $n$ linearly independent active constraints
-- statement:
--   **(Theorem 2.2)** Let $x^*$ be an element of $\mathbb{R}^n$ and let $I = \{i \mid a_i'x^* = b_i\}$ be the set of indices of constraints that are active at $x^*$. Then, the following are equivalent:
--
--   - **(a)** There exist $n$ vectors in the set $\{a_i \mid i \in I\}$, which are linearly independent.
--   - **(b)** The span of the vectors $a_i$, $i \in I$, is all of $\mathbb{R}^n$, that is, every element of $\mathbb{R}^n$ can be expressed as a linear combination of the vectors $a_i$, $i \in I$.
--   - **(c)** The system of equations $a_i'x = b_i$, $i \in I$, has a unique solution.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 2.2, p. 48

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.List.TFAE
import Definitions.Def_ActiveConstraints


open Matrix

/-- **B&T Theorem 2.2 (p. 48).** Equivalent characterizations of "there are
`n` linearly independent constraints active at `x*`". In (c), `x*` itself
solves the active system, so uniqueness is stated as "every solution equals
`x*`". -/

theorem LinearOptimization.lp_active_constraint_equiv {ι : Type} [Fintype ι] {n : ℕ}
    (C : ι → LinearConstraint n) (x' : Fin n → ℝ) :
    List.TFAE
      [ ∃ s : Finset ι, s.card = n ∧ (∀ i ∈ s, (C i).IsActiveAt x') ∧
          LinearIndependent ℝ (fun i : s => (C i.1).a),
        Submodule.span ℝ ((fun i => (C i).a) '' {i | (C i).IsActiveAt x'}) = ⊤,
        ∀ y : Fin n → ℝ,
          (∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ y = (C i).b) → y = x' ] := by
  sorry
