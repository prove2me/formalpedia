-- Prove2me | Theorems.Thm_MatrixAnalytic_BirthDeath_homogeneous_recurrence
-- name    : MatrixAnalytic.BirthDeath.homogeneous_recurrence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:39.332606+00:00
-- url     : https://prove2.me/theorems/c35835f7-b730-45aa-a647-f34c006a0998
-- title:
--   Theorem 4.2.5 — the homogeneous chain (4.9) is recurrent iff a₀ ≤ a₂, positive recurrent iff a₀ < a₂, and G is the minimal nonnegative solution of G = a₂ + a₁G + a₀G²
-- statement:
--   Let $b_0,a_0,a_1,a_2$ satisfy $a_0,a_2>0$, $a_1\ge0$, $b_0+a_0=1$, $a_0+a_1+a_2=1$, and consider the irreducible Markov chain on $\{0,1,2,\dots\}$ with the spatially homogeneous transition matrix (4.9): from $0$ it stays with probability $b_0$ and moves to $1$ with probability $a_0$; from $n\ge1$ it moves to $n-1$, stays, or moves to $n+1$ with probabilities $a_2$, $a_1$, $a_0$. Then:
--
--   1. the chain is recurrent if and only if $a_0\le a_2$;
--   2. it is positive recurrent if and only if $a_0<a_2$;
--   3. for every $n\ge1$, the probability $G\equiv G_n$ of a first passage from state $n$ to state $n-1$ is the minimal nonnegative solution of the equation
--   $$G=a_2+a_1G+a_0G^2. \tag{4.14}$$
--
--   This is the scalar case of the central fact of matrix analytic methods: the first-passage probability is the minimal nonnegative solution of a quadratic equation, while the equation also has the spurious solution $1$ whenever the chain is transient.
--
--   **Formalization Note** Recurrence and positive recurrence are the return-time notions, stated at state $0$ (equivalently every state, by irreducibility). $G_n$ is defined as a sum over taboo trajectories of products of transition probabilities, never as a root of (4.14). "Minimal nonnegative solution" is stated as: $G_n\ge0$, $G_n$ solves (4.14), and $G_n\le x$ for every $x\ge0$ solving (4.14); since such a minimal solution is unique, $G_n$ does not depend on $n$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 92, Theorem 4.2.5, Eq. (4.14)

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain
import Definitions.Def_MatrixAnalytic_BirthDeath_Model
import Definitions.Def_MatrixAnalytic_BirthDeath_Passage

namespace MatrixAnalytic.BirthDeath

theorem homogeneous_recurrence (b₀ a₀ a₁ a₂ : ℝ) (h : IsHomParams b₀ a₀ a₁ a₂) :
    (Recurrent (homP b₀ a₀ a₁ a₂) 0 ↔ a₀ ≤ a₂) ∧
    (PositiveRecurrent (homP b₀ a₀ a₁ a₂) 0 ↔ a₀ < a₂) ∧
    ∀ n : ℕ, 1 ≤ n →
      0 ≤ G (homP b₀ a₀ a₁ a₂) n ∧
      G (homP b₀ a₀ a₁ a₂) n =
        a₂ + a₁ * G (homP b₀ a₀ a₁ a₂) n + a₀ * G (homP b₀ a₀ a₁ a₂) n ^ 2 ∧
      ∀ x : ℝ, 0 ≤ x → x = a₂ + a₁ * x + a₀ * x ^ 2 → G (homP b₀ a₀ a₁ a₂) n ≤ x := by sorry

end MatrixAnalytic.BirthDeath
