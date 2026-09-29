-- Prove2me | Theorems.Thm_LovaszSchrijver_Defect_defect_div_le_NIndex_le_defect
-- name    : LovaszSchrijver.Defect.defect_div_le_NIndex_le_defect
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:56:42.50498+00:00
-- url     : https://prove2.me/theorems/95188301-2d15-469f-9db7-f056d28ca56a
-- title:
--   Theorem 2.13 — r/b ≤ k ≤ r for an inequality with defect r and N-index k
-- statement:
--   Let $G = (V,E)$ be a finite graph with no isolated nodes, and let $a^{\mathsf T}x \le b$ be an inequality with integer coefficients $a \in \mathbb Z_+^V$, $b \in \mathbb Z_+$, valid for $\mathrm{STAB}(G)$, with defect
--   $$r = 2\max\{a^{\mathsf T}x - b : x \in \mathrm{FRAC}(G)\} \ge 0$$
--   and N-index $k$ (the least $t$ such that $a^{\mathsf T}x \le b$ is valid for $N^t(G)$). Then
--   $$\frac{r}{b} \le k \le r,$$
--   stated with the denominator cleared as
--   $$r \le k\,b \qquad\text{and}\qquad k \le r.$$
--
--   The theorem shows that the number of rounds of the Lovász–Schrijver $N$ operator needed to derive a stable set inequality is controlled by how far the fractional stable set polytope violates it: an inequality violated by at most $r/2$ on $\mathrm{FRAC}(G)$ is valid after $r$ rounds, and cannot be valid before $r/b$ rounds.
--
--   **Formalization Note**
--   1. The lower bound is written $r \le k b$ rather than $r/b \le k$. For $b > 0$ the two are equivalent; for $b = 0$ validity for $\mathrm{STAB}(G)$ forces $a = 0$ and $r = 0$, and the cleared form avoids Lean's convention $r/0 = 0$.
--   2. The hypothesis $r \ge 0$ is added. The paper's proof starts "If $r = 0$ we have nothing to prove, so suppose that $r > 0$", presuming $r \ge 0$; without it the upper bound fails (for $x_1 \le 2$ on a single edge, $r = -2$ while $k = 0$). It holds whenever $b = \max\{a^{\mathsf T}x : x \in \mathrm{STAB}(G)\}$, because $\mathrm{STAB}(G) \subseteq \mathrm{FRAC}(G)$.
--   3. The defect and the N-index are given as values $r$, $k$ with `IsGreatest` and `IsLeast` hypotheses, never as a supremum or infimum. Coefficients are natural numbers cast to $\mathbb R$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 182, Theorem 2.13

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_Index

namespace LovaszSchrijver.Defect

theorem defect_div_le_NIndex_le_defect {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℕ) (b : ℕ) (hvalid : Valid (STAB G) (fun i => (a i : ℝ)) b)
    (r : ℝ) (hr : IsDefect G (fun i => (a i : ℝ)) b r) (hr0 : 0 ≤ r)
    (k : ℕ) (hk : IsNIndex G (fun i => (a i : ℝ)) b k) :
    r ≤ k * b ∧ (k : ℝ) ≤ r := by sorry

end LovaszSchrijver.Defect
