-- Prove2me | Theorems.Thm_MatrixAnalytic_BirthDeath_G_R_at_one
-- name    : MatrixAnalytic.BirthDeath.G_R_at_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:45.961258+00:00
-- url     : https://prove2.me/theorems/b8e4eaed-8d44-4846-a37e-5bfefbdab844
-- title:
--   Theorem 4.3.4 — G(1) = min{1, a₂/a₀} and R(1) = min{1, a₀/a₂} for the homogeneous chain
-- statement:
--   Let $b_0,a_0,a_1,a_2$ satisfy $a_0,a_2>0$, $a_1\ge0$, $b_0+a_0=1$, $a_0+a_1+a_2=1$, and consider the spatially homogeneous birth-and-death chain with transition matrix (4.9). Let $G(z)$ be the generating function of the first-passage time from $n$ to $n-1$ and $R(z)$ the generating function of the taboo probabilities of being in $n$, starting from $n-1$, before returning to $n-1$ (both independent of $n\ge1$). Then
--   $$G(1)=\min\{1,a_2/a_0\}\qquad\text{and}\qquad R(1)=\min\{1,a_0/a_2\}.$$
--
--   So the downward passage probability is one exactly when the chain drifts weakly down, and the expected number of visits to $n$ per visit to $n-1$ is one exactly when it drifts weakly up.
--
--   **Formalization Note** The statement is made for every $n\ge1$, with $G(1)=G_n(1)$ and $R(1)=R_n(1)$ the complex generating functions evaluated at $z=1$; the right-hand sides are real numbers viewed as complex numbers.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 98, Theorem 4.3.4

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain
import Definitions.Def_MatrixAnalytic_BirthDeath_Model
import Definitions.Def_MatrixAnalytic_BirthDeath_Passage

namespace MatrixAnalytic.BirthDeath

theorem G_R_at_one (b₀ a₀ a₁ a₂ : ℝ) (h : IsHomParams b₀ a₀ a₁ a₂) (n : ℕ) (hn : 1 ≤ n) :
    Gz (homP b₀ a₀ a₁ a₂) n 1 = ((min 1 (a₂ / a₀) : ℝ) : ℂ) ∧
    Rz (homP b₀ a₀ a₁ a₂) n 1 = ((min 1 (a₀ / a₂) : ℝ) : ℂ) := by sorry

end MatrixAnalytic.BirthDeath
