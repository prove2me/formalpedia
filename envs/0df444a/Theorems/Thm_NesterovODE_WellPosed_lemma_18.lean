-- Prove2me | Theorems.Thm_NesterovODE_WellPosed_lemma_18
-- name    : NesterovODE.WellPosed.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:09.535721+00:00
-- url     : https://prove2.me/theorems/0ded4930-9d03-431d-8be5-87d984478c34
-- title:
--   Lemma 18, p. 30 — uniform boundedness and equicontinuity
-- statement:
--   Let $f\in\mathcal F_L$ and $x_0\in\mathbb R^n$. For each nonnegative integer $m$, let $X_m$ be the solution of the smoothed equation (31) with $\delta_m=\sqrt{3/L}/2^m$. On the common interval $I=[0,\sqrt{6/L}]$, the family $\{X_m|_I:m\ge0\}$ is uniformly bounded and equicontinuous:
--   $$
--   \sup_{m\ge0,\ t\in I}\|X_m(t)\|<\infty,
--   \qquad
--   \{X_m|_I:m\ge0\}\text{ is equicontinuous}.
--   $$
--   This is the compactness input for the existence result.
--
--   **Formalization Note** The statement quantifies over a family of solutions at precisely the page's smoothing scales. Uniform boundedness is an existential common real bound; equicontinuity is restricted to $I$.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 30, Lemma 18

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting

namespace NesterovODE.WellPosed

/-- Lemma 18, p. 30: the specified smoothed family is uniformly bounded and equicontinuous. -/
theorem lemma_18 {n : ℕ} (f : E n → ℝ) (L : NNReal) (x₀ : E n)
    (X V : ℕ → ℝ → E n) (hf : IsFL f L)
    (hX : ∀ m : ℕ,
      IsSmoothedSolution f (Real.sqrt (3 / (L : ℝ)) / (2 : ℝ) ^ m) x₀ (X m) (V m)) :
    (∃ B : ℝ, ∀ (m : ℕ) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) (Real.sqrt (6 / (L : ℝ))) → ‖X m t‖ ≤ B) ∧
    EquicontinuousOn X (Set.Icc (0 : ℝ) (Real.sqrt (6 / (L : ℝ)))) := by sorry

end NesterovODE.WellPosed
