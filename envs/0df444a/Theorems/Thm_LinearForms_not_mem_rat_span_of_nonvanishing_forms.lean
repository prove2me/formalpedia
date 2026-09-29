-- Prove2me | Theorems.Thm_LinearForms_not_mem_rat_span_of_nonvanishing_forms
-- name    : LinearForms.not_mem_rat_span_of_nonvanishing_forms
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T20:46:07.769256+00:00
-- url     : https://prove2.me/theorems/f4cda4ce-33c5-41aa-9f22-92d3da36f048
-- title:
--   Nonvanishing-forms criterion: $y\notin\mathbb Q+\mathbb Q x$ from small nonzero linear forms
-- statement:
--   This is the "nonvanishing forms" (two consecutive forms) criterion for a real number not to lie in the rational span of $1$ and another real number.
--
--   Let $x,y\in\mathbb R$ and let $(p_n)_{n\ge0}$, $(q_n)_{n\ge0}$, $(r_n)_{n\ge0}$ be sequences of integers. For each $n$ consider the linear form and its height
--   $$
--   L_n = p_n + q_n x + r_n y, \qquad H_n = |q_n| + |r_n| .
--   $$
--   Assume
--
--   1. $L_n \neq 0$ for every $n$;
--   2. $L_n \to 0$ as $n\to\infty$;
--   3. the cross terms of two consecutive forms tend to zero:
--   $$
--   |L_n|\,H_{n+1} + |L_{n+1}|\,H_n \;\longrightarrow\; 0 \qquad (n\to\infty).
--   $$
--
--   Then $y$ is not a $\mathbb Q$-linear combination of $1$ and $x$:
--   $$
--   y \neq \alpha + \beta x \qquad \text{for all } \alpha,\beta\in\mathbb Q .
--   $$
--   No irrationality assumption on $x$ is needed.
--
--   This is a variant of the classical linear-forms irrationality criterion (compare Nesterenko's criterion, which Rivoal (Michigan Math. J. 61 (2012), Thm 1) uses to prove the $\mathbb Q$-linear independence of $1, e^z, E(z)$ for rational $z\ne0$) in which the determinant nondegeneracy condition on three consecutive coefficient vectors is replaced by the much easier-to-check condition that no form vanishes. It is meant as the final step of constructions of simultaneous Padé-type approximations to $1,x,y$, where the forms are explicitly nonzero (e.g. $|L_n|\asymp C^n/(n!)^2$ with heights $H_n\asymp C^n n!$), so that only positivity of the forms and decay of the cross terms must be verified.
--
--   **Formalization Note** The quantities $L_n$ and $H_n$ are written inline (with integer coefficients cast to $\mathbb R$) rather than as definitions; the limits are `Filter.Tendsto … atTop (𝓝 0)`.
-- source:
--   Standard elementary linear-forms criterion (cf. Rivoal, Michigan Math. J. 61 (2012), proof of Thm 1, and Nesterenko's criterion); complete proof in the accompanying submission.

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology

theorem LinearForms.not_mem_rat_span_of_nonvanishing_forms (x y : ℝ) (p q r : ℕ → ℤ)
    (h0 : ∀ n, (p n : ℝ) + q n * x + r n * y ≠ 0)
    (h1 : Tendsto (fun n : ℕ => (p n : ℝ) + q n * x + r n * y) atTop (𝓝 0))
    (h2 : Tendsto (fun n : ℕ =>
      |(p n : ℝ) + q n * x + r n * y| * (|(q (n + 1) : ℝ)| + |(r (n + 1) : ℝ)|)
        + |(p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y| * (|(q n : ℝ)| + |(r n : ℝ)|))
      atTop (𝓝 0)) :
    ∀ α β : ℚ, y ≠ α + β * x := by sorry
