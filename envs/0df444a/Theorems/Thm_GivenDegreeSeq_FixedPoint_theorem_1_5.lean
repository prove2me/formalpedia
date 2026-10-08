-- Prove2me | Theorems.Thm_GivenDegreeSeq_FixedPoint_theorem_1_5
-- name    : GivenDegreeSeq.FixedPoint.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:51.505132+00:00
-- url     : https://prove2.me/theorems/e1174fe0-aa48-4d27-a22d-b3a3dd2876ae
-- title:
--   Theorem 1.5 — the iteration $x_{k+1}=\varphi(x_k)$ converges geometrically to the unique $\beta$-model MLE, and has a divergent subsequence when no MLE exists
-- statement:
--   Let $n\ge3$ and let $d_1,\dots,d_n>0$. Let $\varphi:\mathbb R^n\to\mathbb R^n$ be given by
--   $$\varphi_i(x)=\log d_i-\log\sum_{j\ne i}\frac{1}{e^{-x_j}+e^{x_i}},$$
--   and, for $x_0\in\mathbb R^n$, let $x_{k+1}=\varphi(x_k)$ for $k=0,1,2,\dots$. There are functions $\Theta,C:\mathbb R^2\to\mathbb R$, with $0\le\Theta<1$ and $C$ continuous, which do not depend on $n$ or $d$, such that the following hold.
--
--   1. Suppose the maximum likelihood equations
--   $$d_i=\sum_{j\ne i}\frac{e^{\hat\beta_i+\hat\beta_j}}{1+e^{\hat\beta_i+\hat\beta_j}},\qquad i=1,\dots,n,\tag{3}$$
--   have a solution $\hat\beta$. Then $\hat\beta$ is a fixed point of $\varphi$; for every $x_0$ and every $k\ge0$,
--   $$|x_k-\hat\beta|_\infty\le\Theta(|\hat\beta|_\infty,|x_0|_\infty)^{\lfloor k/2\rfloor}\,|x_0-\hat\beta|_\infty,$$
--   so $x_k\to\hat\beta$ geometrically fast at a rate depending only on $(|\hat\beta|_\infty,|x_0|_\infty)$; $\hat\beta$ is the unique solution of (3); and for every $x_0$,
--   $$|x_0-\hat\beta|_\infty\le C(|\hat\beta|_\infty,|x_0|_\infty)\,|x_0-x_1|_\infty.$$
--   2. Conversely, if (3) has no solution, then for every $x_0$ the sequence $\{x_k\}$ is unbounded in the sup norm, i.e. it has a divergent subsequence.
--
--   This is the paper's algorithmic result: iterating $\varphi$ computes the maximum likelihood estimate of the $\beta$-model with a dimension-free geometric rate, certifies its accuracy through the computable quantity $|x_0-x_1|_\infty$, and detects non-existence of the MLE.
--
--   **Formalization Note** The functions $\Theta$ and $C$ are chosen before $n$, $d$, $\hat\beta$ and $x_0$, which is how "the rate depends only on $(|\hat\beta|_\infty,|x_0|_\infty)$" and "$C$ is a continuous function of the pair" are rendered. Geometric convergence is stated through the two-step contraction factor, $\Theta^{\lfloor k/2\rfloor}$ (natural-number division $k/2$). A sequence in $\mathbb R^n$ has a subsequence with $|x_{k_j}|_\infty\to\infty$ exactly when it is unbounded, so "a divergent subsequence" is stated as unboundedness. The hypothesis $n\ge3$ is not on the page but is required: for $n=2$ any solution of (3) comes with a whole line of solutions, so uniqueness fails. The degrees are arbitrary positive reals (the proof uses nothing else); $\log d_i$ requires $d_i>0$. Vertices are `Fin n`, and $|\cdot|_\infty$ is Mathlib's sup norm on `Fin n → ℝ`.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 9, Theorem 1.5 (proof §2, pp. 11–14)

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

namespace GivenDegreeSeq.FixedPoint

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
        (∀ βhat : Fin n → ℝ, MLEq d βhat →
          phi d βhat = βhat ∧
          (∀ (x₀ : Fin n → ℝ) (k : ℕ),
            ‖(phi d)^[k] x₀ - βhat‖ ≤ Θ ‖βhat‖ ‖x₀‖ ^ (k / 2) * ‖x₀ - βhat‖) ∧
          (∀ b : Fin n → ℝ, MLEq d b → b = βhat) ∧
          (∀ x₀ : Fin n → ℝ, ‖x₀ - βhat‖ ≤ C ‖βhat‖ ‖x₀‖ * ‖x₀ - phi d x₀‖)) ∧
        ((¬ ∃ b : Fin n → ℝ, MLEq d b) →
          ∀ x₀ : Fin n → ℝ, ¬ BddAbove (Set.range fun k : ℕ => ‖(phi d)^[k] x₀‖)) := by sorry

end GivenDegreeSeq.FixedPoint
