-- Prove2me | Theorems.Thm_MinimaxRegretRL_Hoeffding_count_deviation
-- name    : MinimaxRegretRL.Hoeffding.count_deviation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:22:53.922934+00:00
-- url     : https://prove2.me/theorems/9ef90364-ca40-4d2b-a7c1-bb167708fa21
-- title:
--   Proof of Lemma 1 — transition-count deviation before Eq. (11)
-- statement:
--   Fix a state-action-next-state triple $(x,a,y)$. The visits to $(x,a)$ before episode $k$ form an adaptive sample count $N_k(x,a)$, and $N_k(x,a,y)$ counts the visits followed by $y$. For every $\delta>0$, the probability that some episode with $N_k(x,a)>0$ violates
--
--   $$|N_k(x,a,y)-N_k(x,a)P(y\mid x,a)|\le\sqrt{2N_k(x,a)P(y\mid x,a)(1-P(y\mid x,a))\ln(2T/\delta)}+\frac{2\ln(2T/\delta)}{3},\qquad T=KH,$$
--
--   is at most $\delta$. The product $P(y\mid x,a)(1-P(y\mid x,a))$ is the variance of the indicator of the next state being $y$.
--
--   **Formalization Note** This is the display before (11), which retains the factor $2$ under the radical. Printed (11) omits that factor after division by $N_k(x,a)$.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 17, proof of Lemma 1, display before Eq. (11)

import Mathlib
import Definitions.Def_MinimaxRegretRL_Hoeffding_Analysis

namespace MinimaxRegretRL.Hoeffding

/-- Proof of Lemma 1, p. 17, display preceding (11), with the factor `2`
under the square root. The printed (11) drops that factor and is not used. -/
theorem count_deviation {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) (x : S) (a : A) (y : S) :
    probEvent M H K δ sel init (fun ω => ∃ k : Fin K,
      0 < nAt M H K δ sel init ω k x a ∧
      Real.sqrt
          (2 * (nAt M H K δ sel init ω k x a : ℝ) *
            (M.P x a y * (1 - M.P x a y)) *
            Real.log (2 * (K * H : ℕ) / δ)) +
        2 * Real.log (2 * (K * H : ℕ) / δ) / 3 <
        |(nyAt M H K δ sel init ω k x a y : ℝ) -
          (nAt M H K δ sel init ω k x a : ℝ) * M.P x a y|) ≤ δ := by sorry

end MinimaxRegretRL.Hoeffding
