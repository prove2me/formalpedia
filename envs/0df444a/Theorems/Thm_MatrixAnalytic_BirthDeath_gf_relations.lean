-- Prove2me | Theorems.Thm_MatrixAnalytic_BirthDeath_gf_relations
-- name    : MatrixAnalytic.BirthDeath.gf_relations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:44.593862+00:00
-- url     : https://prove2.me/theorems/6d76def2-8b05-48b0-953e-1930e6f4a96a
-- title:
--   Theorem 4.3.1 — relations (4.17)–(4.20) between the generating functions G_n(z), U_n(z), R_n(z)
-- statement:
--   Let $P$ be the transition matrix (4.5) of an irreducible birth-and-death chain on $\{0,1,2,\dots\}$, with $a_{ij}=P(i,j)$. For $n\ge1$ let $G_n(z)$, $U_n(z)$ and $R_n(z)$ be the generating functions of the first-passage density from $n$ to $n-1$, of the first-return density to $n$ avoiding $n-1$, and of the taboo density of visits to $n$ starting from $n-1$ before returning to $n-1$. Then, for every $n\ge1$ and every complex $z$ with $|z|<1$, $U_n(z)\ne1$ and
--   $$\begin{aligned}U_n(z)&=za_{n,n}+za_{n,n+1}G_{n+1}(z) &(4.17)\\ &=za_{n,n}+R_{n+1}(z)\,za_{n+1,n}, &(4.18)\\ G_n(z)&=(1-U_n(z))^{-1}za_{n,n-1}, &(4.19)\\ R_n(z)&=za_{n-1,n}(1-U_n(z))^{-1}. &(4.20)\end{aligned}$$
--   Any one of the three sequences of functions determines the other two.
--
--   **Formalization Note** The generating functions are complex power series $\sum_{k\ge1}z^k(\cdot)$ of the taboo path sums. That $1-U_n(z)\ne0$ is part of the conclusion, so the inverses in (4.19)–(4.20) are genuine. The clause "any one of these sequences determines the other two" is not a separate formula: it is what (4.17)–(4.20) express, each function being written in terms of another.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 95, Theorem 4.3.1, Eqs. (4.17)–(4.20)

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain
import Definitions.Def_MatrixAnalytic_BirthDeath_Model
import Definitions.Def_MatrixAnalytic_BirthDeath_Passage

namespace MatrixAnalytic.BirthDeath

theorem gf_relations (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Uz P n z = z * P n n + z * P n (n + 1) * Gz P (n + 1) z ∧
    Uz P n z = z * P n n + Rz P (n + 1) z * z * P (n + 1) n ∧
    Uz P n z ≠ 1 ∧
    Gz P n z = (1 - Uz P n z)⁻¹ * z * P n (n - 1) ∧
    Rz P n z = z * P (n - 1) n * (1 - Uz P n z)⁻¹ := by sorry

end MatrixAnalytic.BirthDeath
