-- Prove2me | Theorems.Thm_LinearOptimization_simplex_terminal_classification
-- name    : LinearOptimization.simplex_terminal_classification
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-06T03:51:00.371223+00:00
-- url     : https://prove2.me/theorems/23d7ef2c-c0be-413e-9a49-8a523fa90638
-- title:
--   Terminal simplex states are optimal or unbounded
-- statement:
--   Consider the standard-form linear program $\min\{c^{\mathsf T}x:Ax=b,\ x\ge 0\}$ with linearly independent rows of $A$. Let $(B,x)$ be a simplex state from which no admissible simplex pivot exists. Then exactly the stopping alternatives needed by the simplex method are available: either $B$ is an optimal basis and $x$ is globally optimal, or there is a feasible recession direction $d$ such that
--
--   $$
--   Ad=0,\qquad d\ge0,\qquad c^{\mathsf T}d<0,\qquad \inf_{y:Ay=b,\ y\ge0}c^{\mathsf T}y=-\infty.
--   $$
--
--   This theorem isolates the terminal classification step: nonnegative reduced costs give the optimality certificate, while a negative reduced cost whose pivot column has no positive entry gives an unbounded ray.
--
--   **Formalization Note** The optimal value is `EReal`-valued, so unboundedness below is expressed by `lpValue c (stdPolyhedron A b) = ⊥`.
-- source:
--   Dimitris Bertsimas and John N. Tsitsiklis, Introduction to Linear Optimization (Athena Scientific, 1997), simplex stopping criteria and Theorem 3.3(a,b), p. 91.

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_SimplexPivot
import Definitions.Def_LinearOptimization_OptimalBasis

open Matrix

theorem LinearOptimization.simplex_terminal_classification {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ)
    (hstate : IsSimplexState A b B x)
    (hterminal : ¬∃ (B' : Fin m ↪ Fin n) (x' : Fin n → ℝ),
      IsSimplexPivot A c B x B' x') :
    (IsOptimalBasis A b c B ∧ IsLpOptimal c (stdPolyhedron A b) x) ∨
      ∃ d : Fin n → ℝ, A.mulVec d = 0 ∧ 0 ≤ d ∧ c ⬝ᵥ d < 0 ∧
        lpValue c (stdPolyhedron A b) = ⊥ := by
  sorry
