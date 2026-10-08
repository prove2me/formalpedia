-- Prove2me | Theorems.Thm_MangasarianFJ_GenFJ_motzkin_transposition
-- name    : MangasarianFJ.GenFJ.motzkin_transposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:25:48.135731+00:00
-- url     : https://prove2.me/theorems/3eb0911a-acef-4f58-bbea-c47eeed54194
-- title:
--   Motzkin's transposition theorem, p. 39 — exactly one of y'A < 0, y'B ≤ 0, y'C = 0 and Az₁ + Bz₂ + Cz₃ = 0, z₁ ≥ 0, z₁ ≠ 0, z₂ ≥ 0 is solvable
-- statement:
--   Let $A$, $B$, $C$ be real matrices with $n$ rows and $a$, $b$, $c$ columns respectively, with $A$ nonempty ($a\ge 1$). Then exactly one of the following two systems has a solution:
--
--   $$
--   \text{(1.5)}\quad y'A<0,\qquad y'B\le 0,\qquad y'C=0 \qquad (y\in E^n),
--   $$
--
--   $$
--   \text{(1.6)}\quad Az_1+Bz_2+Cz_3=0,\qquad z_1\ge 0,\quad z_1\ne 0,\quad z_2\ge 0 \qquad (z_1\in E^a,\ z_2\in E^b,\ z_3\in E^c).
--   $$
--
--   Here $y'A<0$ means that every component of the row vector $y'A$ is negative, $y'B\le 0$ that every component of $y'B$ is nonpositive, and $z_1\ge0$, $z_2\ge0$ are componentwise.
--
--   This theorem of the alternative is the linear-algebra tool that converts the non-solvability of a system of strict linear inequalities into the existence of nonnegative multipliers, as in Lemma 2 and the constraint qualification of §3.
--
--   **Formalization Note** A matrix is given by its family of columns $A_1,\dots,A_a\in E^n$, so the components of $y'A$ are the inner products $\langle y,A_i\rangle$ and $Az_1=\sum_i (z_1)_i A_i$. "Either … or …, but never both" is the exclusive or `Xor`. The hypothesis $a\ge1$ is the page's "A being nonempty"; $b=0$ and $c=0$ (empty $B$, $C$) are allowed.
-- source:
--   Mangasarian and Fromovitz, The Fritz John necessary optimality conditions in the presence of equality and inequality constraints, J. Math. Anal. Appl. 17 (1967), p. 39, MOTZKIN'S TRANSPOSITION THEOREM, (1.5)–(1.6)

import Mathlib

namespace MangasarianFJ.GenFJ
theorem motzkin_transposition {n a b c : ℕ} (ha : 0 < a)
    (A : Fin a → EuclideanSpace ℝ (Fin n)) (B : Fin b → EuclideanSpace ℝ (Fin n))
    (C : Fin c → EuclideanSpace ℝ (Fin n)) :
    Xor
      (∃ y : EuclideanSpace ℝ (Fin n),
        (∀ i, inner ℝ y (A i) < 0) ∧ (∀ i, inner ℝ y (B i) ≤ 0) ∧ ∀ i, inner ℝ y (C i) = 0)
      (∃ (z₁ : Fin a → ℝ) (z₂ : Fin b → ℝ) (z₃ : Fin c → ℝ),
        ∑ i, z₁ i • A i + ∑ i, z₂ i • B i + ∑ i, z₃ i • C i = 0 ∧
        (∀ i, 0 ≤ z₁ i) ∧ z₁ ≠ 0 ∧ ∀ i, 0 ≤ z₂ i) := by sorry
end MangasarianFJ.GenFJ
