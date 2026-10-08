-- Prove2me | Theorems.Thm_GomoryGroup_Rel_lemma_short_optimal
-- name    : GomoryGroup.Rel.lemma_short_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:29:47.104217+00:00
-- url     : https://prove2.me/theorems/1ec61c6c-68d5-4c0f-ade4-ecfda7a03459
-- title:
--   LEMMA, p. 263 — the group problem (4) has an optimal solution with Σ y_i ≤ D − 1
-- statement:
--   Let $B$ be a nonsingular integer $m\times m$ matrix and $N$ an integer $m\times n$ matrix such that every unit vector of $\mathbb Z^m$ is a column of $B$ or of $N$ (the paper's $A=(A',I)$), let $c_B\in\mathbb R^m$, $c_N\in\mathbb R^n$ be such that all relative costs are nonpositive, $c^*_{i+m}\le0$ for $i=1,\dots,n$ ($B$ is an optimal basis), and let $b\in\mathbb Z^m$. Then the group problem (4) has an optimal solution $y\in\mathbb N^n$ with
--   $$\sum_{i=1}^ny_i\le D-1,\qquad D=|\det B|.$$
--
--   The bound on the total size of $y$ is what keeps $Ny$ short, which in turn places $b-Ny$ inside $K^B$ when $b$ is deep inside the cone.
--
--   **Formalization Note** The two standing assumptions of the paper are hypotheses: $A=(A',I)$ makes (4) feasible for every $b$, and $c^*\le0$ ("all $c^*_i$ associated with an optimal basis are $\le0$", p. 262) makes its maximum exist. $D-1$ is natural-number subtraction, harmless since $D\ge1$. Column $j$ of $N$ is $\alpha_{m+1+j}$.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 263, LEMMA

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem lemma_short_optimal {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) (hI : HasUnitColumns B N) (hopt : ∀ j, reducedCost B N cB cN j ≤ 0) :
    ∃ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y ∧ ∑ j, y j ≤ detD B - 1 := by sorry

end GomoryGroup.Rel
