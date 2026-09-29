-- Prove2me | Theorems.Thm_LinearForms_not_mem_rat_span_of_det_forms
-- name    : LinearForms.not_mem_rat_span_of_det_forms
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T18:04:41.979672+00:00
-- url     : https://prove2.me/theorems/23adb22e-94de-4933-89c8-2f7fcfcb19c2
-- title:
--   Determinant criterion: $y\notin\mathbb Q+\mathbb Q x$ from small nondegenerate linear forms
-- statement:
--   This is the determinant (three consecutive linear forms) criterion for a real number not to lie in the rational span of $1$ and another real number.
--
--   Let $x,y\in\mathbb R$ and let $(p_n)_{n\ge0}$, $(q_n)_{n\ge0}$, $(r_n)_{n\ge0}$ be sequences of integers. For each $n$ consider the linear form and its height
--   $$
--   L_n = p_n + q_n x + r_n y, \qquad H_n = |q_n| + |r_n|,
--   $$
--   and put
--   $$
--   S_n = \bigl(|L_n| + |L_{n+1}| + |L_{n+2}|\bigr)\bigl(H_n + H_{n+1} + H_{n+2}\bigr).
--   $$
--   Assume
--
--   1. for infinitely many $n$ the three consecutive coefficient vectors are linearly independent, i.e.
--   $$
--   \det\begin{pmatrix} p_n & q_n & r_n\\ p_{n+1} & q_{n+1} & r_{n+1}\\ p_{n+2} & q_{n+2} & r_{n+2}\end{pmatrix}\neq 0;
--   $$
--   2. $S_n \to 0$ as $n\to\infty$.
--
--   Then $y$ is not a $\mathbb Q$-linear combination of $1$ and $x$:
--   $$
--   y \neq \alpha + \beta x \qquad \text{for all } \alpha,\beta\in\mathbb Q .
--   $$
--   No irrationality assumption on $x$ is needed.
--
--   This is the linear-forms version of the classical irrationality criterion, used when one constructs simultaneous rational approximations (for example Apéry-type or Padé-type recurrences) to the numbers $1, x, y$: a sequence of small integer linear forms, nondegenerate in the determinant sense, rules out any rational linear relation $y = \alpha + \beta x$. It is designed to be reused as the final step of such constructions, where one only has to verify the determinant condition and the decay of $S_n$.
--
--   **Formalization Note** The determinant condition is stated as `∃ᶠ n in atTop, det ≠ 0` for the integer matrix `!![p n, q n, r n; …]`, and the decay condition as convergence of the displayed real sequence $S_n$ to $0$ along `atTop`. The quantities $L_n$ and $H_n$ are written inline rather than as definitions.
-- source:
--   Standard elementary lemma (determinant / linear-forms irrationality criterion for Q-linear independence of 1, x, y); complete proof in the accompanying submission.

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology

theorem LinearForms.not_mem_rat_span_of_det_forms (x y : ℝ) (p q r : ℕ → ℤ)
    (hdet : ∃ᶠ n in atTop,
      (!![p n, q n, r n; p (n + 1), q (n + 1), r (n + 1); p (n + 2), q (n + 2), r (n + 2)] :
        Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0)
    (hS : Tendsto (fun n : ℕ =>
      (|(p n : ℝ) + q n * x + r n * y| + |(p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y|
        + |(p (n + 2) : ℝ) + q (n + 2) * x + r (n + 2) * y|) *
      ((|(q n : ℝ)| + |(r n : ℝ)|) + (|(q (n + 1) : ℝ)| + |(r (n + 1) : ℝ)|)
        + (|(q (n + 2) : ℝ)| + |(r (n + 2) : ℝ)|))) atTop (𝓝 0)) :
    ∀ α β : ℚ, y ≠ α + β * x := by sorry
