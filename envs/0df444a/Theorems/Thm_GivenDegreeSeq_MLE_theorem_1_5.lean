-- Prove2me | Theorems.Thm_GivenDegreeSeq_MLE_theorem_1_5
-- name    : GivenDegreeSeq.MLE.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:17.350772+00:00
-- url     : https://prove2.me/theorems/7037e3cd-29ea-435d-8ca6-ebbaa39410e4
-- title:
--   Theorem 1.5 — the iteration $x_{k+1}=\varphi(x_k)$ converges geometrically to the unique MLE, with $|x_0-\hat\beta|_\infty\le C|x_0-x_1|_\infty$
-- statement:
--   Let $n\ge 3$ and let $d_1,\dots,d_n>0$. Let $\varphi$ be the map of (4)–(5) and, for $x_0\in\mathbb R^n$, let $x_{k+1}=\varphi(x_k)$. There are functions $\theta(a,b)\in[0,1)$ and $C(a,b)$, with $C$ continuous, which do not depend on $n$ or $d$, such that:
--
--   1. If the ML equations (3) have a solution $\hat\beta$, then $\hat\beta$ is a fixed point of $\varphi$; for every $x_0$ and $k$,
--   $$|x_k-\hat\beta|_\infty\le\theta\big(|\hat\beta|_\infty,|x_0|_\infty\big)^{\lfloor k/2\rfloor}\,|x_0-\hat\beta|_\infty;$$
--   $\hat\beta$ is the unique solution of (3); and for every $x_0$,
--   $$|x_0-\hat\beta|_\infty\le C\big(|\hat\beta|_\infty,|x_0|_\infty\big)\,|x_0-x_1|_\infty.$$
--   2. If (3) has no solution, then for every $x_0$ the sequence $(x_k)$ is unbounded, i.e. it has a subsequence with $|x_{k_j}|_\infty\to\infty$.
--
--   In this mission the theorem supplies the uniqueness of the MLE and, through the a-priori bound with $x_0=\beta$, its distance to the true parameter.
--
--   **Formalization Note** This restates the goal of mission 1 of the series in this mission's namespace with the same statement shape (drafts cannot import drafts), including the hypotheses $n\ge 3$ (at $n=2$ solutions of (3) form a line) and $d_i>0$ (needed for $\log d_i$). Geometric convergence is expressed by the factor $\theta^{\lfloor k/2\rfloor}$; "divergent subsequence" by unboundedness. To be replaced by a reference item once mission 1 is published.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 9, Theorem 1.5

import Mathlib
import Definitions.Def_GivenDegreeSeq_MLE_Basic

namespace GivenDegreeSeq.MLE

/-- Theorem 1.5, p. 9. There are functions `Θ(a, b) ∈ [0, 1)` and `C(a, b)`, `C` continuous,
both independent of `n` and `d`, such that for every `n ≥ 3` and every positive degree vector
`d`, with `x_k = φ^k(x₀)`:
* if `β̂` solves the ML equations (3), then `β̂` is a fixed point of `φ`;
  `|x_k − β̂|∞ ≤ Θ(|β̂|∞, |x₀|∞)^{⌊k/2⌋} |x₀ − β̂|∞` for every `x₀` and `k`
  (geometric convergence at a rate depending only on `(|β̂|∞, |x₀|∞)`);
  `β̂` is the unique solution of (3); and
  `|x₀ − β̂|∞ ≤ C(|β̂|∞, |x₀|∞) |x₀ − x₁|∞` for every `x₀`;
* if (3) has no solution, then for every `x₀` the sequence `(x_k)` is unbounded, i.e. has a
  subsequence with `|x_{k_j}|∞ → ∞` (a divergent subsequence). -/
theorem theorem_1_5 :
    ∃ Θ C : ℝ → ℝ → ℝ, (∀ a b, 0 ≤ Θ a b ∧ Θ a b < 1) ∧ Continuous (Function.uncurry C) ∧
      ∀ n : ℕ, 3 ≤ n → ∀ d : Fin n → ℝ, (∀ i, 0 < d i) →
        (∀ βhat : Fin n → ℝ, GivenDegreeSeq.FixedPoint.MLEq d βhat →
          GivenDegreeSeq.FixedPoint.phi d βhat = βhat ∧
          (∀ (x₀ : Fin n → ℝ) (k : ℕ),
            ‖(GivenDegreeSeq.FixedPoint.phi d)^[k] x₀ - βhat‖ ≤ Θ ‖βhat‖ ‖x₀‖ ^ (k / 2) * ‖x₀ - βhat‖) ∧
          (∀ b : Fin n → ℝ, GivenDegreeSeq.FixedPoint.MLEq d b → b = βhat) ∧
          (∀ x₀ : Fin n → ℝ, ‖x₀ - βhat‖ ≤ C ‖βhat‖ ‖x₀‖ * ‖x₀ - GivenDegreeSeq.FixedPoint.phi d x₀‖)) ∧
        ((¬ ∃ b : Fin n → ℝ, GivenDegreeSeq.FixedPoint.MLEq d b) →
          ∀ x₀ : Fin n → ℝ, ¬ BddAbove (Set.range fun k : ℕ => ‖(GivenDegreeSeq.FixedPoint.phi d)^[k] x₀‖)) := by sorry

end GivenDegreeSeq.MLE
