-- Prove2me | Theorems.Thm_MatrixAnalytic_BirthDeath_homogeneous_geometric
-- name    : MatrixAnalytic.BirthDeath.homogeneous_geometric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:42.549435+00:00
-- url     : https://prove2.me/theorems/8900ba47-8cd7-4d15-a316-bf67be7a86ea
-- title:
--   Theorem 4.2.4 — the spatially homogeneous chain (4.9) has R_n ≡ R and, when positive recurrent, a geometric stationary distribution with R = a₀/a₂
-- statement:
--   Let $b_0,a_0,a_1,a_2$ satisfy $a_0,a_2>0$, $a_1\ge0$, $b_0+a_0=1$, $a_0+a_1+a_2=1$, and consider the irreducible, aperiodic Markov chain on $\{0,1,2,\dots\}$ with the spatially homogeneous transition matrix (4.9): from $0$ it stays with probability $b_0$ and moves to $1$ with probability $a_0$; from $n\ge1$ it moves to $n-1$, stays, or moves to $n+1$ with probabilities $a_2$, $a_1$, $a_0$. Let $\pi=(\pi_0,\pi_1,\dots)$ be its vector of limit probabilities and $R_n$ the expected number of visits to $n$ between two successive visits to $n-1$. Then $R_n=R$ does not depend on $n\ge1$, and
--   $$\pi_n=\pi_{n-1}R\qquad\text{for all }n\ge1.$$
--   In particular, if the chain is positive recurrent, then $R=a_0/a_2$ and the stationary distribution is the geometric density
--   $$\pi_n=(1-R)R^n,\qquad n\ge0.$$
--
--   **Formalization Note** The limit probabilities are given as a vector $\pi$ with $P^k(0,n)\to\pi_n$ for every $n$. Independence of $n$ is stated as $R_{n}=R_1$ for all $n\ge1$, and $R$ denotes $R_1$. Positive recurrence is stated at state $0$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 91, Theorem 4.2.4

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain
import Definitions.Def_MatrixAnalytic_BirthDeath_Model
import Definitions.Def_MatrixAnalytic_BirthDeath_Passage

namespace MatrixAnalytic.BirthDeath

theorem homogeneous_geometric (b₀ a₀ a₁ a₂ : ℝ) (h : IsHomParams b₀ a₀ a₁ a₂)
    (hap : AperiodicC (homP b₀ a₀ a₁ a₂)) (π : ℕ → ℝ)
    (hπ : ∀ n : ℕ, Filter.Tendsto (fun k : ℕ => stepPow (homP b₀ a₀ a₁ a₂) k 0 n)
      Filter.atTop (nhds (π n))) :
    (∀ n : ℕ, R (homP b₀ a₀ a₁ a₂) (n + 1) = R (homP b₀ a₀ a₁ a₂) 1) ∧
    (∀ n : ℕ, π (n + 1) = π n * R (homP b₀ a₀ a₁ a₂) 1) ∧
    (PositiveRecurrent (homP b₀ a₀ a₁ a₂) 0 →
      R (homP b₀ a₀ a₁ a₂) 1 = a₀ / a₂ ∧
      ∀ n : ℕ, π n = (1 - R (homP b₀ a₀ a₁ a₂) 1) * R (homP b₀ a₀ a₁ a₂) 1 ^ n) := by sorry

end MatrixAnalytic.BirthDeath
