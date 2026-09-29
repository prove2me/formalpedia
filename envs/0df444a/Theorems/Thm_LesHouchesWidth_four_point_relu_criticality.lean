-- Prove2me | Theorems.Thm_LesHouchesWidth_four_point_relu_criticality
-- name    : LesHouchesWidth.four_point_relu_criticality
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:19:39.964228+00:00
-- url     : https://prove2.me/theorems/986765a0-9c58-41a1-9515-46e8cca267f9
-- title:
--   Theorem 4.2 at criticality (ReLU): $\kappa_4^{(L+1)}/(K^{(L+1)})^2=C_\sigma L/n+O_L(n^{-2})$
-- statement:
--   For ReLU networks, $\sigma(t)=\max(t,0)$, tuned to criticality with $C_b=0$ and $C_W=2$, there is a constant $C_\sigma$ such that for every depth $L\ge1$, all $n_0,n_{L+1}\ge1$ and every input $x\neq0$ there is $C$ with
--   $$\bigg|\frac{\kappa^{(L+1)}_4}{\big(K^{(L+1)}\big)^2}-C_\sigma\frac{L}{n}\bigg|\le\frac{C}{n^2}$$
--   for all uniform hidden widths $n_1=\cdots=n_L=n\ge1$.
--
--   At criticality the normalized four-point function grows linearly in the effective depth $L/n$.
--
--   **Formalization Note** The notes state this for any $\sigma$ tuned to criticality. It is formalized for ReLU, where the critical kernel is constant in depth. For $\tanh$ the notes' statement is asymptotic in depth.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 33, Theorem 4.2 ("Thus, at criticality and uniform width ..."); criticality for ReLU ($C_b=0$, $C_W=2$) from Theorem 4.1, p. 32.

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP
import Definitions.Def_LesHouchesWidth_FiniteWidth

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem four_point_relu_criticality :
    ∃ Cσ : ℝ, ∀ (L : ℕ), 1 ≤ L → ∀ (n0 nOut : ℕ), 1 ≤ n0 → 1 ≤ nOut →
      ∀ x : Fin n0 → ℝ, x ≠ 0 → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        ∀ i : Fin (uniformWidths n0 nOut L N (L + 1)),
          |kappa4 0 2 (fun t => max t 0) (uniformWidths n0 nOut L N) L x (L + 1) i /
              nngpKernel 0 2 (fun t => max t 0) (L + 1) x x ^ 2 - Cσ * L / N|
            ≤ C / (N : ℝ) ^ 2 := by sorry

end LesHouchesWidth
