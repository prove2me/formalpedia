-- Prove2me | Theorems.Thm_MinimaxRegretRL_Hoeffding_eq9_bernstein
-- name    : MinimaxRegretRL.Hoeffding.eq9_bernstein
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:22:43.653523+00:00
-- url     : https://prove2.me/theorems/a04e359f-5bf2-4eea-902c-67d446644a78
-- title:
--   Proof of Lemma 1, Eq. (9) — Bernstein bound at adaptive sample counts
-- statement:
--   Fix a step $h$ and state-action pair $(x,a)$. In the UCBVI-CH interaction, let $N_k(x,a)$ be the number of visits before episode $k$, and let $\mathbb V_h^*(x,a)$ be the variance of $V_h^*(Y)$ for $Y\sim P(\cdot\mid x,a)$. For every $\delta>0$, the probability that some episode with $N_k(x,a)>0$ violates
--
--   $$\left|[(P-\widehat P_k)V_h^*](x,a)\right|\le\sqrt{\frac{2\mathbb V_h^*(x,a)\ln(2T/\delta)}{N_k(x,a)}}+\frac{2H\ln(2T/\delta)}{3N_k(x,a)},\qquad T=KH,$$
--
--   is at most $\delta$. This supplies the true-variance concentration component of the empirical-model event.
--
--   **Formalization Note** The probability statement holds simultaneously over episode starts for the fixed $h,x,a$; zero counts are excluded from the displayed fractions. Step $h$ is zero-based in Lean.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 17, proof of Lemma 1, Eq. (9)

import Mathlib
import Definitions.Def_MinimaxRegretRL_Hoeffding_Analysis

namespace MinimaxRegretRL.Hoeffding

/-- Proof of Lemma 1, Eq. (9), p. 17. For a fixed step and pair, the
Bernstein bound holds simultaneously at all episode starts with positive
sample count. The book's `h` is zero-based here. -/
theorem eq9_bernstein {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) (h : Fin H) (x : S) (a : A) :
    probEvent M H K δ sel init (fun ω => ∃ k : Fin K,
      0 < nAt M H K δ sel init ω k x a ∧
      Real.sqrt
          (2 * trueVariance M H h.val x a * Real.log (2 * (K * H : ℕ) / δ) /
            nAt M H K δ sel init ω k x a) +
        2 * (H : ℝ) * Real.log (2 * (K * H : ℕ) / δ) /
          (3 * nAt M H K δ sel init ω k x a) <
        |∑ y : S, (M.P x a y - phatAt M H K δ sel init ω k x a y) *
          optimalValue M H h.val y|) ≤ δ := by sorry

end MinimaxRegretRL.Hoeffding
