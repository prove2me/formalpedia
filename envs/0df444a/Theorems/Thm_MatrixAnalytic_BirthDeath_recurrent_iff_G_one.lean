-- Prove2me | Theorems.Thm_MatrixAnalytic_BirthDeath_recurrent_iff_G_one
-- name    : MatrixAnalytic.BirthDeath.recurrent_iff_G_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:47.854133+00:00
-- url     : https://prove2.me/theorems/3be1d5b6-fcc4-4d5b-9d0f-d307dbfdcb00
-- title:
--   Lemma 4.2.2 — a birth-and-death chain is recurrent iff G₁ = 1
-- statement:
--   Let $P$ be the transition matrix (4.5) of an irreducible discrete-time birth-and-death chain on $\{0,1,2,\dots\}$: $P$ is stochastic, tridiagonal, and $a_{i,i+1}>0$, $a_{i+1,i}>0$ for all $i\ge0$. Let $G_1$ be the probability that the chain, started in state $1$, reaches state $0$ in a finite time. Then the chain is recurrent if and only if
--   $$G_1 = 1.$$
--
--   This reduces recurrence of the whole chain to a single first-passage probability, and is the starting point of the classification of birth-and-death chains in Section 4.2.
--
--   **Formalization Note** Recurrence is stated at state $0$ (return to $0$ with probability one); by irreducibility it is the same for every state. $G_1$ is the sum over $k\ge1$ of the taboo path sums $g_1(k)$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 90, Lemma 4.2.2

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain
import Definitions.Def_MatrixAnalytic_BirthDeath_Model
import Definitions.Def_MatrixAnalytic_BirthDeath_Passage

namespace MatrixAnalytic.BirthDeath

theorem recurrent_iff_G_one (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) :
    Recurrent P 0 ↔ G P 1 = 1 := by sorry

end MatrixAnalytic.BirthDeath
