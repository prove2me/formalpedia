-- Prove2me | Theorems.Thm_NonlinCG_PropStar_lemma_4_1
-- name    : NonlinCG.PropStar.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:20.126888+00:00
-- url     : https://prove2.me/theorems/72c5335f-66a7-4f41-b891-de036b17cd4e
-- title:
--   Lemma 4.1 — with β_k ≥ 0, Zoutendijk and sufficient descent, gradients bounded away from 0 force Σ‖u_k − u_{k−1}‖² < ∞
-- statement:
--   Let $f$ satisfy Assumptions 2.1 at the starting point $x_1$ and let $(x_k, d_k, \beta_k, \alpha_k)$ be a run of the conjugate gradient iteration (1.2)–(1.3) with $\beta_k \ge 0$ for all $k \ge 2$. Suppose the line search satisfies the Zoutendijk condition
--   $\sum_{k\ge1} \langle g_k, d_k\rangle^2/\|d_k\|^2 < \infty$ (2.7) and the sufficient descent condition $\langle g_k, d_k\rangle \le -\sigma_3\|g_k\|^2$ for all $k \ge 1$ (4.1), with $0 < \sigma_3 \le 1$. If the gradients are bounded away from zero, i.e. there is $\gamma > 0$ with $\|g_k\| \ge \gamma$ for all $k \ge 1$ (4.3), then $d_k \ne 0$ for all $k \ge 1$ and, with $u_k := d_k/\|d_k\|$,
--
--   $$\sum_{k \ge 2} \|u_k - u_{k-1}\|^2 < \infty. \qquad (4.5)$$
--
--   The lemma says that, as long as the gradients stay away from zero, the normalized search directions change more and more slowly. It is the first of the two ingredients of the proof by contradiction of Theorem 4.3. Its hypotheses are expected to be contradictory on every actual run (that is what Theorem 4.3 shows); the lemma is a step of that argument.
--
--   **Formalization Note** The paper's standing smoothness assumption "$f$ is smooth" (1.1) is stated as global continuous differentiability, in addition to Assumptions 2.1. The run has positive steplengths and is indexed from $1$. The Zoutendijk sum is written as $\sum_k \langle g_k,d_k\rangle^2/\|d_k\|^2$, which equals $\sum_k \cos^2\theta_k\|g_k\|^2$ where the latter is defined. The series (4.5) is stated as the summability of $k \mapsto \|u_{k+2} - u_{k+1}\|^2$ over $k \ge 0$. As in the paper, neither (4.4) nor Property (\*) is assumed.
-- source:
--   Gilbert & Nocedal, Global convergence properties of conjugate gradient methods for optimization, INRIA Rapport de Recherche 1268 (June 1990), HAL inria-00075291v1, p. 12, Lemma 4.1 (4.5); (4.1), (4.3) on p. 11

import Mathlib
import Definitions.Def_NonlinCG_PropStar_Setting

namespace NonlinCG.PropStar

/-- Lemma 4.1 (p. 12). Under Assumptions 2.1, for a run of (1.2)–(1.3) with `β_k ≥ 0`, a line
search satisfying the Zoutendijk condition (2.7) and the sufficient descent condition (4.1), if
the gradients are bounded away from zero (4.3), then `d_k ≠ 0` and
`Σ_{k≥2} ‖u_k − u_{k−1}‖² < ∞` (4.5), where `u_k := d_k/‖d_k‖`. -/
theorem lemma_4_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₃ : ℝ)
    (hA : NonlinCG.FRBound.Assumptions21 f (x 1)) (hrun : NonlinCG.FRBound.IsCGRun f β α x d)
    (hβ : ∀ k ≥ 2, 0 ≤ β k)
    (hZ : NonlinCG.FRBound.ZoutendijkCondition f x d)
    (hσ₃ : 0 < σ₃ ∧ σ₃ ≤ 1) (hD : SufficientDescent f σ₃ x d)
    (h43 : ∃ γ > 0, ∀ k ≥ 1, γ ≤ ‖NonlinCG.FRBound.g f x k‖) :
    (∀ k ≥ 1, d k ≠ 0) ∧
      Summable (fun k : ℕ => ‖u d (k + 2) - u d (k + 1)‖ ^ 2) := by sorry

end NonlinCG.PropStar
